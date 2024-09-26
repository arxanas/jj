// Copyright 2023 The Jujutsu Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Filesystem monitor tool interface.
//!
//! Interfaces with a filesystem monitor tool to efficiently query for
//! filesystem updates, without having to crawl the entire working copy. This is
//! particularly useful for large working copies, or for working copies for
//! which it's expensive to materialize files, such those backed by a network or
//! virtualized filesystem.

#![warn(missing_docs)]

use std::path::PathBuf;

use config::Config;
use config::ConfigError;

use crate::settings::ConfigResultExt;

/// Config for Watchman filesystem monitor (<https://facebook.github.io/watchman/>).
#[derive(Default, Eq, PartialEq, Clone, Debug)]
pub struct WatchmanConfig {
    /// Whether to use triggers to monitor for changes in the background.
    pub register_trigger: bool,
}

/// The recognized kinds of filesystem monitors.
#[derive(Eq, PartialEq, Clone, Debug)]
pub enum FsmonitorSettings {
    /// The Watchman filesystem monitor (<https://facebook.github.io/watchman/>).
    Watchman(WatchmanConfig),

    // @nocommit: document
    GitStatus,

    /// Only used in tests.
    Test {
        /// The set of changed files to pretend that the filesystem monitor is
        /// reporting.
        changed_files: Vec<PathBuf>,
    },

    /// No filesystem monitor. This is the default if nothing is configured, but
    /// also makes it possible to turn off the monitor on a case-by-case basis
    /// when the user gives an option like
    /// `--config-toml='core.fsmonitor="none"'`; useful when e.g. when doing
    /// analysis of snapshot performance.
    None,
}

impl FsmonitorSettings {
    /// Creates an `FsmonitorSettings` from a `config`.
    pub fn from_config(config: &Config) -> Result<FsmonitorSettings, ConfigError> {
        match config.get_string("core.fsmonitor") {
            Ok(s) => match s.as_str() {
                "watchman" => Ok(Self::Watchman(WatchmanConfig {
                    register_trigger: config
                        .get_bool("core.watchman.register_snapshot_trigger")
                        .optional()?
                        .unwrap_or_default(),
                })),
                "git-status" => Ok(Self::GitStatus),
                "test" => Err(ConfigError::Message(
                    "cannot use test fsmonitor in real repository".to_string(),
                )),
                "none" => Ok(Self::None),
                other => Err(ConfigError::Message(format!(
                    "unknown fsmonitor kind: {other}",
                ))),
            },
            Err(ConfigError::NotFound(_)) => Ok(Self::None),
            Err(err) => Err(err),
        }
    }
}

/// Filesystem monitor integration using Watchman
/// (<https://facebook.github.io/watchman/>). Requires `watchman` to already be
/// installed on the system.
#[cfg(feature = "watchman")]
pub mod watchman {
    use std::path::Path;
    use std::path::PathBuf;

    use itertools::Itertools;
    use thiserror::Error;
    use tracing::info;
    use tracing::instrument;
    use watchman_client::expr;
    use watchman_client::prelude::Clock as InnerClock;
    use watchman_client::prelude::ClockSpec;
    use watchman_client::prelude::NameOnly;
    use watchman_client::prelude::QueryRequestCommon;
    use watchman_client::prelude::QueryResult;
    use watchman_client::prelude::TriggerRequest;

    /// Represents an instance in time from the perspective of the filesystem
    /// monitor.
    ///
    /// This can be used to perform incremental queries. When making a query,
    /// the result will include an associated "clock" representing the time
    /// that the query was made.  By passing the same clock into a future
    /// query, we inform the filesystem monitor that we only wish to get
    /// changed files since the previous point in time.
    #[derive(Clone, Debug)]
    pub struct Clock(InnerClock);

    impl From<crate::protos::working_copy::WatchmanClock> for Clock {
        fn from(clock: crate::protos::working_copy::WatchmanClock) -> Self {
            use crate::protos::working_copy::watchman_clock::WatchmanClock;
            let watchman_clock = clock.watchman_clock.unwrap();
            let clock = match watchman_clock {
                WatchmanClock::StringClock(string_clock) => {
                    InnerClock::Spec(ClockSpec::StringClock(string_clock))
                }
                WatchmanClock::UnixTimestamp(unix_timestamp) => {
                    InnerClock::Spec(ClockSpec::UnixTimestamp(unix_timestamp))
                }
            };
            Self(clock)
        }
    }

    impl From<Clock> for crate::protos::working_copy::WatchmanClock {
        fn from(clock: Clock) -> Self {
            use crate::protos::working_copy::watchman_clock;
            use crate::protos::working_copy::WatchmanClock;
            let Clock(clock) = clock;
            let watchman_clock = match clock {
                InnerClock::Spec(ClockSpec::StringClock(string_clock)) => {
                    watchman_clock::WatchmanClock::StringClock(string_clock)
                }
                InnerClock::Spec(ClockSpec::UnixTimestamp(unix_timestamp)) => {
                    watchman_clock::WatchmanClock::UnixTimestamp(unix_timestamp)
                }
                InnerClock::ScmAware(_) => {
                    unimplemented!("SCM-aware Watchman clocks not supported")
                }
            };
            WatchmanClock {
                watchman_clock: Some(watchman_clock),
            }
        }
    }

    #[allow(missing_docs)]
    #[derive(Debug, Error)]
    pub enum Error {
        #[error("Could not connect to Watchman")]
        WatchmanConnectError(#[source] watchman_client::Error),

        #[error("Could not canonicalize working copy root path")]
        CanonicalizeRootError(#[source] std::io::Error),

        #[error("Watchman failed to resolve the working copy root path")]
        ResolveRootError(#[source] watchman_client::Error),

        #[error("Failed to query Watchman")]
        WatchmanQueryError(#[source] watchman_client::Error),

        #[error("Failed to register Watchman trigger")]
        WatchmanTriggerError(#[source] watchman_client::Error),
    }

    /// Handle to the underlying Watchman instance.
    pub struct Fsmonitor {
        client: watchman_client::Client,
        resolved_root: watchman_client::ResolvedRoot,
    }

    impl Fsmonitor {
        /// Initialize the Watchman filesystem monitor. If it's not already
        /// running, this will start it and have it crawl the working
        /// copy to build up its in-memory representation of the
        /// filesystem, which may take some time.
        #[instrument]
        pub async fn init(
            working_copy_path: &Path,
            config: &super::WatchmanConfig,
        ) -> Result<Self, Error> {
            info!("Initializing Watchman filesystem monitor...");
            let connector = watchman_client::Connector::new();
            let client = connector
                .connect()
                .await
                .map_err(Error::WatchmanConnectError)?;
            let working_copy_root = watchman_client::CanonicalPath::canonicalize(working_copy_path)
                .map_err(Error::CanonicalizeRootError)?;
            let resolved_root = client
                .resolve_root(working_copy_root)
                .await
                .map_err(Error::ResolveRootError)?;

            let monitor = Fsmonitor {
                client,
                resolved_root,
            };

            // Registering the trigger causes an unconditional evaluation of the query, so
            // test if it is already registered first.
            if !config.register_trigger {
                monitor.unregister_trigger().await?;
            } else if !monitor.is_trigger_registered().await? {
                monitor.register_trigger().await?;
            }
            Ok(monitor)
        }

        /// Query for changed files since the previous point in time.
        ///
        /// The returned list of paths is relative to the `working_copy_path`.
        /// If it is `None`, then the caller must crawl the entire working copy
        /// themselves.
        #[instrument(skip(self))]
        pub async fn query_changed_files(
            &self,
            previous_clock: Option<Clock>,
        ) -> Result<(Clock, Option<Vec<PathBuf>>), Error> {
            // TODO: might be better to specify query options by caller, but we
            // shouldn't expose the underlying watchman API too much.
            info!("Querying Watchman for changed files...");
            let QueryResult {
                version: _,
                is_fresh_instance,
                files,
                clock,
                state_enter: _,
                state_leave: _,
                state_metadata: _,
                saved_state_info: _,
                debug: _,
            }: QueryResult<NameOnly> = self
                .client
                .query(
                    &self.resolved_root,
                    QueryRequestCommon {
                        since: previous_clock.map(|Clock(clock)| clock),
                        expression: Some(self.build_exclude_expr()),
                        ..Default::default()
                    },
                )
                .await
                .map_err(Error::WatchmanQueryError)?;

            let clock = Clock(clock);
            if is_fresh_instance {
                // The Watchman documentation states that if it was a fresh
                // instance, we need to delete any tree entries that didn't appear
                // in the returned list of changed files. For now, the caller will
                // handle this by manually crawling the working copy again.
                Ok((clock, None))
            } else {
                let paths = files
                    .unwrap_or_default()
                    .into_iter()
                    .map(|NameOnly { name }| name.into_inner())
                    .collect_vec();
                Ok((clock, Some(paths)))
            }
        }

        /// Return whether or not a trigger has been registered already.
        #[instrument(skip(self))]
        pub async fn is_trigger_registered(&self) -> Result<bool, Error> {
            info!("Checking for an existing Watchman trigger...");
            Ok(self
                .client
                .list_triggers(&self.resolved_root)
                .await
                .map_err(Error::WatchmanTriggerError)?
                .triggers
                .iter()
                .any(|t| t.name == "jj-background-monitor"))
        }

        /// Register trigger for changed files.
        #[instrument(skip(self))]
        async fn register_trigger(&self) -> Result<(), Error> {
            info!("Registering Watchman trigger...");
            self.client
                .register_trigger(
                    &self.resolved_root,
                    TriggerRequest {
                        name: "jj-background-monitor".to_string(),
                        command: vec![
                            "jj".to_string(),
                            "debug".to_string(),
                            "snapshot".to_string(),
                        ],
                        expression: Some(self.build_exclude_expr()),
                        ..Default::default()
                    },
                )
                .await
                .map_err(Error::WatchmanTriggerError)?;
            Ok(())
        }

        /// Register trigger for changed files.
        #[instrument(skip(self))]
        async fn unregister_trigger(&self) -> Result<(), Error> {
            info!("Unregistering Watchman trigger...");
            self.client
                .remove_trigger(&self.resolved_root, "jj-background-monitor")
                .await
                .map_err(Error::WatchmanTriggerError)?;
            Ok(())
        }

        /// Build an exclude expr for `working_copy_path`.
        fn build_exclude_expr(&self) -> expr::Expr {
            // TODO: consider parsing `.gitignore`.
            let exclude_dirs = [Path::new(".git"), Path::new(".jj")];
            let excludes = itertools::chain(
                // the directories themselves
                [expr::Expr::Name(expr::NameTerm {
                    paths: exclude_dirs.iter().map(|&name| name.to_owned()).collect(),
                    wholename: true,
                })],
                // and all files under the directories
                exclude_dirs.iter().map(|&name| {
                    expr::Expr::DirName(expr::DirNameTerm {
                        path: name.to_owned(),
                        depth: None,
                    })
                }),
            )
            .collect();
            expr::Expr::Not(Box::new(expr::Expr::Any(excludes)))
        }
    }
}

pub mod git_status {
    use core::str;
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};
    use std::process::{Command, ExitStatus, Stdio};

    use itertools::Itertools;
    use thiserror::Error;

    use crate::backend::CommitId;

    #[allow(missing_docs)]
    #[derive(Debug, Error)]
    pub enum Error {
        #[error("failed to spawn {} {}: {err}", program.to_string_lossy(), args.into_iter().map(|arg| arg.to_string_lossy()).join(" "))]
        SpawnGitStatus {
            program: OsString,
            args: Vec<OsString>,
            #[source]
            err: std::io::Error,
        },

        #[error("failed to run {} {}: {status}", program.to_string_lossy(), args.into_iter().map(|arg| arg.to_string_lossy()).join(" "))]
        GitStatusFailed {
            program: OsString,
            args: Vec<OsString>,
            status: ExitStatus,
        },

        #[error("failed to compile regexes (should not happen): {err}")]
        CompileRegexes {
            #[source]
            err: regex::Error,
        },

        #[error("failed to parse status entry {entry_num}: {message}: {entry:?}")]
        Parse {
            message: String,
            entry_num: usize,
            entry: String,
        },

        #[error("failed to decode UTF-8: {err}: {buf:?}")]
        DecodeCommitUtf8 {
            buf: Vec<u8>,

            #[source]
            err: std::str::Utf8Error,
        },

        #[error("failed to decode commit as hex: {err}: {hex:?}")]
        DecodeCommitHex {
            hex: String,

            #[source]
            err: hex::FromHexError,
        },

        #[error("internal bug when parsing git status output: {message}")]
        Bug { message: String },
    }

    /// One of the dirty files in the working copy according to `git status`.
    ///
    /// NOTE(arxanas, 2024-09-26): This just contains the path of the file for
    /// now; we could include more stuff like the hash, rename-tracking, etc. in
    /// the future.
    #[derive(Debug)]
    pub struct StatusFile {
        /// The path to the file. @nocommit: relative to repo root?
        pub path: PathBuf,
    }

    #[derive(Debug)]
    pub struct StatusOutput {
        pub head_commit_id: Option<CommitId>,
        pub files: Vec<StatusFile>,
    }

    /// From the Git docs:
    ///
    /// > Show untracked files. When -u option is not used, untracked files and
    /// > directories are shown (i.e. the same as specifying normal), to help you
    /// > avoid forgetting to add newly created files. Because it takes extra work
    /// > to find untracked files in the filesystem, this mode may take some time
    /// > in a large working tree.
    #[derive(Clone, Copy, Debug)]
    pub enum UntrackedFilesMode {
        /// Show no untracked files.
        No,

        /// Show untracked files and directories.
        Normal,

        /// Also show individual files in untracked directories.
        All,
    }

    /// From the Git docs:
    ///
    /// > The mode parameter is used to specify the handling of ignored files.
    /// > When matching mode is specified, paths that explicitly match an ignored
    /// > pattern are shown. If a directory matches an ignore pattern, then
    /// > it is shown, but not paths contained in the ignored directory. If a
    /// > directory does not match an ignore pattern, but all contents are
    /// > ignored, then the directory is not shown, but all contents are shown.
    #[derive(Clone, Copy, Debug)]
    pub enum IgnoredMode {
        /// Shows ignored files and directories, unless --untracked-files=all is specified, in which case individual files in ignored directories are displayed.
        Traditional,

        /// Show no ignored files.
        No,

        /// Shows ignored files and directories matching an ignore pattern.
        Matching,
    }

    /// Options to pass to `git status`.
    #[derive(Clone, Debug)]
    pub struct StatusOptions {
        /// Whether to include untracked files in the output.
        pub untracked_files: UntrackedFilesMode,

        /// Whether to include ignored files in the output.
        pub ignored: IgnoredMode,
    }

    fn process_status_entries(
        status_entries: Vec<porcelain_v2::StatusEntry>,
    ) -> Result<StatusOutput, Error> {
        let mut head_commit_id = None;
        let mut status_files = Vec::new();
        for status_entry in status_entries {
            match status_entry {
                porcelain_v2::StatusEntry::Header { key, value } => {
                    if &key == b"branch.oid" {
                        head_commit_id = if value == b"initial" {
                            None
                        } else {
                            let value =
                                str::from_utf8(&value).map_err(|err| Error::DecodeCommitUtf8 {
                                    buf: value.clone(),
                                    err,
                                })?;
                            let commit_id = CommitId::try_from_hex(value).map_err(|err| {
                                Error::DecodeCommitHex {
                                    hex: value.to_string(),
                                    err,
                                }
                            })?;
                            Some(commit_id)
                        }
                    }
                }
                porcelain_v2::StatusEntry::Ordinary { path, .. }
                | porcelain_v2::StatusEntry::RenamedOrCopied {
                    path,
                    original_path: _, // currently unused
                    ..
                }
                | porcelain_v2::StatusEntry::Unmerged { path, .. }
                | porcelain_v2::StatusEntry::Untracked { path } => {
                    status_files.push(StatusFile { path });
                }
                porcelain_v2::StatusEntry::Ignored { path: _ } => {
                    // Do nothing.
                }
            }
        }
        Ok(StatusOutput {
            head_commit_id,
            files: status_files,
        })
    }

    pub fn query_git_status(
        git_exe_path: &Path,
        repo_path: &Path,
        status_options: StatusOptions,
    ) -> Result<StatusOutput, Error> {
        let StatusOptions {
            untracked_files,
            ignored,
        } = status_options;
        let mut command = Command::new(git_exe_path);

        command
            .arg("-C")
            .arg(repo_path)
            .arg("status")
            .arg("--porcelain=v2")
            // use the null character to terminate entries so that we can handle
            // filenames with newlines
            .arg("-z")
            // enable "branch" header lines, which will tell us what the base commit OID is
            .arg("--branch")
            .arg(match untracked_files {
                UntrackedFilesMode::No => "--untracked-files=no",
                UntrackedFilesMode::Normal => "--untracked-files=normal",
                UntrackedFilesMode::All => "--untracked-files=all",
            })
            .arg(match ignored {
                IgnoredMode::Traditional => "--ignored=traditional",
                IgnoredMode::No => "--ignored=no",
                IgnoredMode::Matching => "--ignored=matching",
            })
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::null());

        let program: OsString = command.get_program().to_owned();
        let args: Vec<OsString> = command.get_args().map(|arg| arg.to_owned()).collect();
        tracing::debug!(?command, "running git status");
        let output = command.output().map_err(|err| Error::SpawnGitStatus {
            program: program.clone(),
            args: args.clone(),
            err,
        })?;
        if !output.status.success() {
            return Err(Error::GitStatusFailed {
                program,
                args,
                status: output.status,
            });
        }
        let status_entries = parse_git_status_porcelain_v2_output(output.stdout)?;
        let status_output = process_status_entries(status_entries)?;
        Ok(status_output)
    }

    /// Encodings of the raw data as specified in `git-status(2)` section
    /// "Porcelain Format Version 2".
    ///
    /// NOTE(arxanas, 2024-09-26): Most fields aren't currently used. It might
    /// be nice to one day upstream this to
    /// https://github.com/gitext-rs/git2-ext
    #[allow(dead_code, missing_docs)]
    mod porcelain_v2 {
        use std::path::PathBuf;

        #[derive(Debug)]
        pub enum ChangeType {
            Unmodified,
            Modified,
            FileTypeChanged,
            Added,
            Deleted,
            Renamed,
            Copied,
            UpdatedButUnmerged,
            Invalid,
        }

        impl From<char> for ChangeType {
            fn from(value: char) -> Self {
                match value {
                    ' ' | '.' => ChangeType::Unmodified,
                    'M' => ChangeType::Modified,
                    'T' => ChangeType::FileTypeChanged,
                    'A' => ChangeType::Added,
                    'D' => ChangeType::Deleted,
                    'R' => ChangeType::Renamed,
                    'C' => ChangeType::Copied,
                    'U' => ChangeType::UpdatedButUnmerged,
                    _ => ChangeType::Invalid,
                }
            }
        }

        #[derive(Debug)]
        pub enum SubmoduleState {
            NotASubmodule,
            Submodule {
                commit_changed: bool,
                has_tracked_changes: bool,
                has_untracked_changes: bool,
            },
        }

        #[derive(Debug)]
        pub struct FileMode(pub u32);

        #[derive(Debug)]
        pub enum RenameOrCopy {
            Rename,
            Copy,
        }

        #[derive(Debug)]
        pub struct ObjectId(pub [char; 40]);

        #[derive(Debug)]
        pub enum StatusEntry {
            Header {
                key: Vec<u8>,
                value: Vec<u8>,
            },
            Ordinary {
                xy: [ChangeType; 2],
                submodule_state: SubmoduleState,
                mode_head: FileMode,
                mode_index: FileMode,
                mode_worktree: FileMode,
                object_head: ObjectId,
                object_index: ObjectId,
                path: PathBuf,
            },
            RenamedOrCopied {
                xy: [ChangeType; 2],
                submodule_state: SubmoduleState,
                mode_head: FileMode,
                mode_index: FileMode,
                mode_worktree: FileMode,
                object_head: ObjectId,
                object_index: ObjectId,
                rename_or_copy: RenameOrCopy,
                similarity_score: usize,
                path: PathBuf,
                original_path: PathBuf,
            },
            Unmerged {
                xy: [ChangeType; 2],
                submodule_state: SubmoduleState,
                mode_stage1: u32,
                mode_stage2: u32,
                mode_stage3: u32,
                object_stage1: ObjectId,
                object_stage2: ObjectId,
                object_stage3: ObjectId,
                path: PathBuf,
            },
            Untracked {
                path: PathBuf,
            },
            Ignored {
                path: PathBuf,
            },
        }
    }

    #[derive(Debug)]
    struct Regexes {
        /// Format: `# <key> <value>\0`
        header: regex::bytes::Regex,

        /// Format: `1 <XY> <sub> <mH> <mI> <mW> <hH> <hI> <path>`
        ordinary: regex::bytes::Regex,

        /// Format: `2 <XY> <sub> <mH> <mI> <mW> <hH> <hI> <X><score> <path><sep><origPath>`
        renamed_or_copied: regex::bytes::Regex,

        /// Format: `u <XY> <sub> <m1> <m2> <m3> <mW> <h1> <h2> <h3> <path>`
        unmerged: regex::bytes::Regex,

        /// Format: `? <path>`
        untracked: regex::bytes::Regex,

        /// Format: `! <path>`
        ignored: regex::bytes::Regex,
    }

    impl Regexes {
        fn new() -> Result<Self, regex::Error> {
            Ok(Self {
                header: regex::bytes::Regex::new(r"^# (?P<key>[^ ]+) (?P<value>[^\x00]+)\x00")?,
                ordinary: regex::bytes::Regex::new(
                    r"^1 (?P<XY>.{2}) (?P<sub>.{4}) (?P<mH>[0-9]+) (?P<mI>[0-9]+) (?P<mW>[0-9]+) (?P<hH>[0-9a-f]{40}) (?P<hI>[0-9a-f]{40}) (?P<path>[^\x00]+)\x00",
                )?,
                renamed_or_copied: regex::bytes::Regex::new(
                    r"^1 (?P<XY>.{2}) (?P<sub>.{4}) (?P<mH>[0-9]+) (?P<mI>[0-9]+) (?P<mW>[0-9]+) (?P<hH>[0-9a-f]{40}) (?P<hI>[0-9a-f]{40}) (?P<X>.)(?P<score>[0-9]+) (?P<path>[^\x00]+)\x00(?P<origPath>[^\x00]+)\x00",
                )?,
                unmerged: regex::bytes::Regex::new(
                    r"^u (?P<XY>.{2}) (?P<sub>.{4}) (?P<m1>[0-9]+) (?P<m2>[0-9]+) (?P<m3>[0-9]+) (?P<mW>[0-9]+) (?P<h1>[0-9a-f]{40}) (?P<h2>[0-9a-f]{40}) (?P<h3>[0-9a-f]{40}) (?P<path>[^\x00]+)\x00",
                )?,
                untracked: regex::bytes::Regex::new(r"^\? (?P<path>[^\x00]+)\x00")?,
                ignored: regex::bytes::Regex::new(r"^! (?P<path>[^\x00]+)\x00")?,
            })
        }
    }

    fn parse_git_status_porcelain_v2_output(
        output: Vec<u8>,
    ) -> Result<Vec<porcelain_v2::StatusEntry>, Error> {
        let regexes = Regexes::new().map_err(|err| Error::CompileRegexes { err })?;
        let mut parse_state = ParseState {
            regexes: &regexes,
            remaining_output: &output,
            entry_num: 0,
        };
        let mut status_entries = Vec::new();
        loop {
            let old_remaining_output = parse_state.remaining_output;
            let (next_parse_state, next_status_entry) = match parse_state.parse_next_status_entry()
            {
                Ok(Some(next)) => next,
                Ok(None) => break,
                Err(err) => {
                    return Err(Error::Parse {
                        message: err.to_string(),
                        entry_num: status_entries.len() + 1,
                        entry: old_remaining_output
                            // FIXME: Technically, renamed entries can have two
                            // null bytes (since there's both the old and new
                            // path), but we only include the contents of the
                            // entry up until the first null byte here. The
                            // included path will be the first (target) path
                            // instead of the second (source) path.
                            .split(|c| *c == 0)
                            .next()
                            .map(|s| String::from_utf8_lossy(s).to_string())
                            .unwrap_or_default(),
                    });
                }
            };

            parse_state = if old_remaining_output == next_parse_state.remaining_output {
                return Err(Error::Bug {
                    message: format!(
                        "git status parser failed to make progress: {next_parse_state:?}"
                    ),
                });
            } else {
                next_parse_state
            };
            status_entries.push(next_status_entry);
        }
        Ok(status_entries)
    }

    #[derive(Clone)]
    struct ParseState<'a> {
        regexes: &'a Regexes,
        remaining_output: &'a [u8],
        // @nocommit: delete and have caller track
        entry_num: usize,
    }

    impl<'a> std::fmt::Debug for ParseState<'a> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let Self {
                regexes,
                remaining_output,
                entry_num,
            } = self;
            f.debug_struct("ParseState")
                .field("regexes", regexes)
                .field("remaining_output", remaining_output)
                .field("entry_num", entry_num)
                .finish()
        }
    }

    impl<'a> ParseState<'a> {
        fn parse_entry_with_regex(
            self,
            regex: &'a regex::bytes::Regex,
            f: impl Fn(regex::bytes::Captures<'a>) -> Result<porcelain_v2::StatusEntry, ParseError>,
        ) -> Result<Option<(Self, porcelain_v2::StatusEntry)>, ParseError> {
            let Self {
                regexes,
                remaining_output,
                entry_num,
            } = self;
            let captures = match regex.captures(remaining_output) {
                Some(captures) => captures,
                None => {
                    return Err(ParseError::RegexMatchFailed {
                        parse_state: self,
                        regex,
                    })
                }
            };
            let remaining_output = &remaining_output[captures.get(0).unwrap().len()..];
            let status_entry = f(captures)?;
            let parse_state = Self {
                regexes,
                remaining_output,
                entry_num: entry_num + 1,
            };
            // @nocommit: remove `Result` from return type
            Ok(Some((parse_state, status_entry)))
        }

        fn get_capture(
            captures: &regex::bytes::Captures<'a>,
            name: &'static str,
        ) -> Result<&'a [u8], ParseError<'a>> {
            captures
                .name(name)
                .map(|m| m.as_bytes())
                .ok_or_else(|| ParseError::Bug {
                    message: format!("expected capture group {name}"),
                })
        }

        fn parse_xy(
            captures: &regex::bytes::Captures<'a>,
            name: &'static str,
        ) -> Result<[porcelain_v2::ChangeType; 2], ParseError<'a>> {
            let bytes = Self::get_capture(captures, name)?;
            let xy = bytes
                .iter()
                .copied()
                .map(char::from)
                .map(porcelain_v2::ChangeType::from)
                .collect_vec();
            xy.try_into().map_err(|_| ParseError::Bug {
                message: format!("expected exactly 2 XY change types, got: {bytes:?}"),
            })
        }

        fn parse_submodule_state(
            captures: &regex::bytes::Captures<'a>,
        ) -> Result<porcelain_v2::SubmoduleState, ParseError<'a>> {
            let bytes = Self::get_capture(captures, "sub")?;
            match bytes {
                [b'N', b'.', b'.', b'.'] => Ok(porcelain_v2::SubmoduleState::NotASubmodule),
                [b'S', c, m, u] => {
                    let commit_changed = match c {
                        b'C' => true,
                        b'.' => false,
                        _ => {
                            return Err(ParseError::Bug {
                                message: format!("unexpected submodule state 'c': {bytes:?}"),
                            });
                        }
                    };
                    let has_tracked_changes = match m {
                        b'M' => true,
                        b'.' => false,
                        _ => {
                            return Err(ParseError::Bug {
                                message: format!("unexpected submodule state 'm': {bytes:?}"),
                            });
                        }
                    };
                    let has_untracked_changes = match u {
                        b'U' => true,
                        b'.' => false,
                        _ => {
                            return Err(ParseError::Bug {
                                message: format!("unexpected submodule state 'u': {bytes:?}"),
                            });
                        }
                    };
                    Ok(porcelain_v2::SubmoduleState::Submodule {
                        commit_changed,
                        has_tracked_changes,
                        has_untracked_changes,
                    })
                }
                bytes => Err(ParseError::Bug {
                    message: format!("unexpected submodule state: {bytes:?}"),
                }),
            }
        }

        fn parse_mode(
            captures: &regex::bytes::Captures<'a>,
            name: &'static str,
        ) -> Result<porcelain_v2::FileMode, ParseError<'a>> {
            let bytes = Self::get_capture(captures, name)?;
            let mode = str::from_utf8(bytes).map_err(|err| ParseError::Bug {
                message: format!("failed to parse mode as UTF-8: {bytes:?}: {err}"),
            })?;
            let mode = u32::from_str_radix(mode, 8).map_err(|err| ParseError::Bug {
                message: format!("failed to parse mode as octal literal: {mode}: {err}"),
            })?;
            Ok(porcelain_v2::FileMode(mode))
        }

        fn parse_object_id(
            captures: &regex::bytes::Captures<'a>,
            name: &'static str,
        ) -> Result<porcelain_v2::ObjectId, ParseError<'a>> {
            let bytes = Self::get_capture(captures, name)?;
            let chars = bytes.iter().copied().map(char::from).collect_vec();
            let chars = chars.try_into().map_err(|_| ParseError::Bug {
                message: format!(
                    "expected 40 hex characters, got {:?}: {bytes:?}",
                    bytes.len()
                ),
            })?;
            Ok(porcelain_v2::ObjectId(chars))
        }

        fn parse_path(
            captures: &regex::bytes::Captures<'a>,
            name: &'static str,
        ) -> Result<PathBuf, ParseError<'a>> {
            let bytes = Self::get_capture(captures, name)?;
            let path = str::from_utf8(bytes).map_err(|err| ParseError::InvalidUtf8Path {
                buf: bytes.to_vec(),
                err,
            })?;
            let path = PathBuf::from(path);
            Ok(path)
        }

        fn parse_rename_or_copy(
            captures: &regex::bytes::Captures<'a>,
            name: &'static str,
        ) -> Result<porcelain_v2::RenameOrCopy, ParseError<'a>> {
            let rename_or_copy = Self::get_capture(captures, name)?;
            let rename_or_copy = match rename_or_copy {
                [b'R'] => porcelain_v2::RenameOrCopy::Rename,
                [b'C'] => porcelain_v2::RenameOrCopy::Copy,
                _ => {
                    return Err(ParseError::Bug {
                        message: "unexpected rename/copy indicator: ".to_string(),
                    })
                }
            };
            Ok(rename_or_copy)
        }

        fn parse_similarity_score(
            captures: &regex::bytes::Captures<'a>,
            name: &'static str,
        ) -> Result<usize, ParseError<'a>> {
            let score = Self::get_capture(captures, name)?;
            let score = str::from_utf8(score).map_err(|err| ParseError::Bug {
                message: format!("failed to parse similarity score as UTF-8: {err}"),
            })?;
            let score = score.parse().map_err(|err| ParseError::Bug {
                message: format!("failed to parse similarity score as integer: {err}"),
            })?;
            Ok(score)
        }

        fn parse_next_status_entry(
            self,
        ) -> Result<Option<(ParseState<'a>, porcelain_v2::StatusEntry)>, ParseError<'a>> {
            match self.remaining_output.get(0) {
                None => Ok(None),

                Some(b'#') => {
                    let regex = &self.regexes.header;
                    self.parse_entry_with_regex(regex, |captures| {
                        Ok(porcelain_v2::StatusEntry::Header {
                            key: Self::get_capture(&captures, "key")?.to_vec(),
                            value: Self::get_capture(&captures, "value")?.to_vec(),
                        })
                    })
                }

                Some(b'1') => {
                    let regex = &self.regexes.ordinary;
                    self.parse_entry_with_regex(regex, |captures| {
                        Ok(porcelain_v2::StatusEntry::Ordinary {
                            xy: Self::parse_xy(&captures, "XY")?,
                            submodule_state: Self::parse_submodule_state(&captures)?,
                            mode_head: Self::parse_mode(&captures, "mH")?,
                            mode_index: Self::parse_mode(&captures, "mI")?,
                            mode_worktree: Self::parse_mode(&captures, "mW")?,
                            object_head: Self::parse_object_id(&captures, "hH")?,
                            object_index: Self::parse_object_id(&captures, "hI")?,
                            path: Self::parse_path(&captures, "path")?,
                        })
                    })
                }

                Some(b'2') => {
                    let regex = &self.regexes.renamed_or_copied;
                    self.parse_entry_with_regex(regex, |captures| {
                        Ok(porcelain_v2::StatusEntry::RenamedOrCopied {
                            xy: Self::parse_xy(&captures, "XY")?,
                            submodule_state: Self::parse_submodule_state(&captures)?,
                            mode_head: Self::parse_mode(&captures, "mH")?,
                            mode_index: Self::parse_mode(&captures, "mI")?,
                            mode_worktree: Self::parse_mode(&captures, "mW")?,
                            object_head: Self::parse_object_id(&captures, "hH")?,
                            object_index: Self::parse_object_id(&captures, "hI")?,
                            rename_or_copy: Self::parse_rename_or_copy(&captures, "X")?,
                            similarity_score: Self::parse_similarity_score(&captures, "score")?,
                            path: Self::parse_path(&captures, "path")?,
                            original_path: Self::parse_path(&captures, "origPath")?,
                        })
                    })
                }

                Some(other) => Err(ParseError::UnknownEntryType {
                    entry_type: char::from(*other),
                }),
            }
        }
    }

    #[derive(Debug, Error)]
    enum ParseError<'a> {
        #[error("regex match failed: {regex}")]
        RegexMatchFailed {
            parse_state: ParseState<'a>,
            regex: &'a regex::bytes::Regex,
        },

        #[error("unknown entry type: {entry_type}")]
        UnknownEntryType { entry_type: char },

        #[error("path was not valid UTF-8: {err}: {buf:?}")]
        InvalidUtf8Path {
            buf: Vec<u8>,

            #[source]
            err: std::str::Utf8Error,
        },

        #[error("{message}")]
        Bug { message: String },
    }
}
