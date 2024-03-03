use crate::cli_util::WorkspaceCommandHelper;
use crate::command_error::CommandError;
use crate::config::CommandNameAndArgs;
use crate::merge_tools::{self, ExternalMergeTool};
const DEFAULT_CONTEXT_LINES: usize = 3;

    /// Number of lines of context to show
    #[arg(long)]
    context: Option<usize>,
    Git { context: usize },
    ColorWords { context: usize },
        Ok(vec![default_diff_format(settings, args.context)?])
        formats.push(default_diff_format(settings, args.context)?);
        (
            args.git,
            DiffFormat::Git {
                context: args.context.unwrap_or(DEFAULT_CONTEXT_LINES),
            },
        ),
        (
            args.color_words,
            DiffFormat::ColorWords {
                context: args.context.unwrap_or(DEFAULT_CONTEXT_LINES),
            },
        ),
        let tool = merge_tools::get_external_tool_config(settings, name)?
            .unwrap_or_else(|| ExternalMergeTool::with_program(name));
        formats.push(DiffFormat::Tool(Box::new(tool)));
fn default_diff_format(
    settings: &UserSettings,
    num_context_lines: Option<usize>,
) -> Result<DiffFormat, config::ConfigError> {
        let tool = if let CommandNameAndArgs::String(name) = &args {
            merge_tools::get_external_tool_config(settings, name)?
        } else {
            None
        .unwrap_or_else(|| ExternalMergeTool::with_diff_args(&args));
        return Ok(DiffFormat::Tool(Box::new(tool)));
        "git" => Ok(DiffFormat::Git {
            context: num_context_lines.unwrap_or(DEFAULT_CONTEXT_LINES),
        }),
        "color-words" => Ok(DiffFormat::ColorWords {
            context: num_context_lines.unwrap_or(DEFAULT_CONTEXT_LINES),
        }),
            DiffFormat::Git { context } => {
                show_git_diff(formatter, workspace_command, *context, tree_diff)?;
            DiffFormat::ColorWords { context } => {
                show_color_words_diff(formatter, workspace_command, *context, tree_diff)?;
    num_context_lines: usize,
    num_context_lines: usize,
                    show_color_words_diff_hunks(
                        &[],
                        &right_content.contents,
                        num_context_lines,
                        formatter,
                    )?;
                        num_context_lines,
                    show_color_words_diff_hunks(
                        &left_content.contents,
                        &[],
                        num_context_lines,
                        formatter,
                    )?;
    num_context_lines: usize,
    for hunk in unified_diff_hunks(left_content, right_content, num_context_lines) {
    num_context_lines: usize,
                show_unified_diff_hunks(formatter, &[], &right_part.content, num_context_lines)?;
                show_unified_diff_hunks(
                    formatter,
                    &left_part.content,
                    &right_part.content,
                    num_context_lines,
                )?;
                show_unified_diff_hunks(formatter, &left_part.content, &[], num_context_lines)?;