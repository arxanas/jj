// Copyright 2022 Google LLC
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

use std::path::PathBuf;

use crate::common::TestEnvironment;

pub mod common;

fn set_up() -> (TestEnvironment, PathBuf) {
    let test_env = TestEnvironment::default();
    let git_repo_path = test_env.env_root().join("git-repo");
    git2::Repository::init(&git_repo_path).unwrap();

    test_env.jj_cmd_success(
        test_env.env_root(),
        &["git", "clone", "git-repo", "jj-repo"],
    );
    let workspace_root = test_env.env_root().join("jj-repo");
    (test_env, workspace_root)
}

#[test]
fn test_git_push_nothing() {
    let (test_env, workspace_root) = set_up();
    // No branches to push yet
    let stdout = test_env.jj_cmd_success(&workspace_root, &["git", "push"]);
    insta::assert_snapshot!(stdout, @r###"
    Nothing changed.
    "###);
}

#[test]
fn test_git_push_open() {
    let (test_env, workspace_root) = set_up();
    // When pushing everything, won't push an open commit even if there's a branch
    // on it
    test_env.jj_cmd_success(&workspace_root, &["branch", "my-branch"]);
    let stdout = test_env.jj_cmd_success(&workspace_root, &["git", "push"]);
    insta::assert_snapshot!(stdout, @r###"
    Skipping branch 'my-branch' since it points to an open commit.
    Nothing changed.
    "###);

    // When pushing a specific branch, won't push it if it points to an open commit
    let stderr =
        test_env.jj_cmd_failure(&workspace_root, &["git", "push", "--branch", "my-branch"]);
    insta::assert_snapshot!(stderr, @r###"
    Error: Won't push open commit
    "###);
    // When pushing with `--change`, won't push if it points to an open commit
    let stderr =
        test_env.jj_cmd_failure(&workspace_root, &["git", "push", "--change", "my-branch"]);
    insta::assert_snapshot!(stderr, @r###"
    Error: Won't push open commit
    "###);
}

#[test]
fn test_git_push_conflict() {
    let (test_env, workspace_root) = set_up();
    std::fs::write(workspace_root.join("file"), "first").unwrap();
    test_env.jj_cmd_success(&workspace_root, &["close", "-m", "first"]);
    std::fs::write(workspace_root.join("file"), "second").unwrap();
    test_env.jj_cmd_success(&workspace_root, &["close", "-m", "second"]);
    std::fs::write(workspace_root.join("file"), "third").unwrap();
    test_env.jj_cmd_success(&workspace_root, &["rebase", "-r", "@", "-d", "@--"]);
    test_env.jj_cmd_success(&workspace_root, &["branch", "my-branch"]);
    test_env.jj_cmd_success(&workspace_root, &["close", "-m", "third"]);
    let stderr = test_env.jj_cmd_failure(&workspace_root, &["git", "push"]);
    insta::assert_snapshot!(stderr, @r###"
    Error: Won't push commit 50ccff1aeab0 since it has conflicts
    "###);
}

#[test]
fn test_git_push_no_description() {
    let (test_env, workspace_root) = set_up();
    test_env.jj_cmd_success(&workspace_root, &["close", "-m", ""]);
    let stderr = test_env.jj_cmd_failure(&workspace_root, &["git", "push", "--change", "@-"]);
    insta::assert_snapshot!(stderr, @r###"
    Error: Won't push commit d386e9a9aced since it has no description
    "###);
}

#[test]
fn test_git_push_missing_author() {
    let (test_env, workspace_root) = set_up();
    test_env
        .jj_cmd(&workspace_root, &["checkout", "root"])
        .env_remove("JJ_USER")
        .assert()
        .success();
    test_env.jj_cmd_success(&workspace_root, &["close", "-m", "initial"]);
    let stderr = test_env.jj_cmd_failure(&workspace_root, &["git", "push", "--change", "@-"]);
    insta::assert_snapshot!(stderr, @r###"
    Error: Won't push commit bb61dfb78ea8 since it has no author set
    "###);
    test_env
        .jj_cmd(&workspace_root, &["checkout", "root"])
        .env_remove("JJ_EMAIL")
        .assert()
        .success();
    test_env.jj_cmd_success(&workspace_root, &["close", "-m", "initial"]);
    let stderr = test_env.jj_cmd_failure(&workspace_root, &["git", "push", "--change", "@-"]);
    insta::assert_snapshot!(stderr, @r###"
    Error: Won't push commit 5d9027bc2f89 since it has no author set
    "###);
}

#[test]
fn test_git_push_missing_committer() {
    let (test_env, workspace_root) = set_up();
    test_env.jj_cmd_success(&workspace_root, &["checkout", "root"]);
    test_env.jj_cmd_success(&workspace_root, &["close", "-m", "initial"]);
    test_env
        .jj_cmd(
            &workspace_root,
            &["describe", "@-", "-m", "no committer name"],
        )
        .env_remove("JJ_USER")
        .assert()
        .success();
    let stderr = test_env.jj_cmd_failure(&workspace_root, &["git", "push", "--change", "@-"]);
    insta::assert_snapshot!(stderr, @r###"
    Error: Won't push commit 10b7c9392952 since it has no committer set
    "###);
    test_env.jj_cmd_success(&workspace_root, &["checkout", "root"]);
    test_env.jj_cmd_success(&workspace_root, &["close", "-m", "initial"]);
    test_env
        .jj_cmd(
            &workspace_root,
            &["describe", "@-", "-m", "no committer email"],
        )
        .env_remove("JJ_EMAIL")
        .assert()
        .success();
    let stderr = test_env.jj_cmd_failure(&workspace_root, &["git", "push", "--change", "@-"]);
    insta::assert_snapshot!(stderr, @r###"
    Error: Won't push commit ba2d25ede939 since it has no committer set
    "###);
}
