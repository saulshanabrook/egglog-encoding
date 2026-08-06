//! Backend-free capture of the parser's lossless physical source grouping.
//!
//! This is the first stage of the standalone frontend mapper. It deliberately
//! copies parser-owned ranges and commands without rendering commands or
//! consulting spans, names, schemas, or any backend state.

use std::error::Error;
use std::fmt::{self, Display, Formatter};

use crate::ast::{Command, ParsedSourceProgram};
use crate::frontend_program::{
    SourceDocument, SourceGroup, SourceGroupId, SourceSubcommand, SourceSubcommandId,
    SourceSubcommandRef,
};

/// Lossless source document plus the still-unresolved commands in each
/// physical transaction group.
#[derive(Clone, Debug)]
pub(crate) struct FrontendSourceSeed {
    pub(crate) document: SourceDocument,
    pub(crate) groups: Vec<FrontendSourceSeedGroup>,
}

#[derive(Clone, Debug)]
pub(crate) struct FrontendSourceSeedGroup {
    pub(crate) id: SourceGroupId,
    pub(crate) subcommands: Vec<FrontendSourceSeedCommand>,
}

#[derive(Clone, Debug)]
pub(crate) struct FrontendSourceSeedCommand {
    pub(crate) source: SourceSubcommandRef,
    pub(crate) command: Command,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum FrontendSourceCaptureError {
    GroupIdentityExhausted {
        ordinal: usize,
    },
    SubcommandIdentityExhausted {
        group: SourceGroupId,
        ordinal: usize,
    },
}

impl Display for FrontendSourceCaptureError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::GroupIdentityExhausted { ordinal } => write!(
                f,
                "physical source group ordinal {ordinal} exceeds the u32 identity space"
            ),
            Self::SubcommandIdentityExhausted { group, ordinal } => write!(
                f,
                "source subcommand ordinal {ordinal} in group {} exceeds the u32 identity space",
                group.ordinal()
            ),
        }
    }
}

impl Error for FrontendSourceCaptureError {}

fn checked_group_id(ordinal: usize) -> Result<SourceGroupId, FrontendSourceCaptureError> {
    let ordinal = u32::try_from(ordinal)
        .map_err(|_| FrontendSourceCaptureError::GroupIdentityExhausted { ordinal })?;
    Ok(SourceGroupId::new(ordinal))
}

fn checked_subcommand_id(
    group: SourceGroupId,
    ordinal: usize,
) -> Result<SourceSubcommandId, FrontendSourceCaptureError> {
    let ordinal = u32::try_from(ordinal)
        .map_err(|_| FrontendSourceCaptureError::SubcommandIdentityExhausted { group, ordinal })?;
    Ok(SourceSubcommandId::new(ordinal))
}

/// Capture exact source bytes, physical groups, and group-local command IDs.
pub(crate) fn capture_source_seed(
    parsed: ParsedSourceProgram,
) -> Result<FrontendSourceSeed, FrontendSourceCaptureError> {
    let mut groups = Vec::with_capacity(parsed.groups.len());
    let mut document_groups = Vec::with_capacity(parsed.groups.len());

    for (group_ordinal, parsed_group) in parsed.groups.into_iter().enumerate() {
        let group_id = checked_group_id(group_ordinal)?;
        let mut subcommands = Vec::with_capacity(parsed_group.commands.len());
        let mut document_subcommands = Vec::with_capacity(parsed_group.commands.len());
        for (subcommand_ordinal, command) in parsed_group.commands.into_iter().enumerate() {
            let subcommand_id = checked_subcommand_id(group_id, subcommand_ordinal)?;
            let source = SourceSubcommandRef::new(group_id, subcommand_id);
            document_subcommands.push(SourceSubcommand { id: subcommand_id });
            subcommands.push(FrontendSourceSeedCommand { source, command });
        }

        document_groups.push(SourceGroup {
            id: group_id,
            leading_trivia: parsed_group.leading_trivia_range,
            command: parsed_group.command_range,
            subcommands: document_subcommands,
        });
        groups.push(FrontendSourceSeedGroup {
            id: group_id,
            subcommands,
        });
    }

    let document = SourceDocument {
        logical_name: parsed.source.name.clone(),
        contents: parsed.source.contents.clone(),
        groups: document_groups,
        eof_trailer: parsed.eof_trailer_range,
    };
    Ok(FrontendSourceSeed { document, groups })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::ast::{Command, Parser, SimpleMacro};

    fn capture(
        parser: &mut Parser,
        logical_name: Option<String>,
        source: &str,
    ) -> FrontendSourceSeed {
        capture_source_seed(
            parser
                .get_program_from_string_grouped(logical_name, source)
                .unwrap(),
        )
        .unwrap()
    }

    #[test]
    fn capture_is_lossless_for_unicode_trivia_and_eof() {
        let input = " \t; λ lead\n(print-size) ; α between\n(print-size)\n; Ω trailer";
        let seed = capture(
            &mut Parser::default(),
            Some("unicode.egg".to_owned()),
            input,
        );

        assert_eq!(seed.document.logical_name.as_deref(), Some("unicode.egg"));
        assert_eq!(seed.document.contents, input);
        assert_eq!(seed.groups.len(), 2);
        let mut reconstructed = String::new();
        for group in &seed.document.groups {
            reconstructed.push_str(&seed.document.contents[group.leading_trivia.clone()]);
            reconstructed.push_str(&seed.document.contents[group.command.clone()]);
        }
        reconstructed.push_str(&seed.document.contents[seed.document.eof_trailer.clone()]);
        assert_eq!(reconstructed, input);
        assert_ne!(
            seed.document.groups[1].command.start,
            input[..seed.document.groups[1].command.start]
                .chars()
                .count()
        );
    }

    #[test]
    fn parser_macro_subcommands_share_one_group_and_local_ids_reset() {
        let mut parser = Parser::default();
        parser.add_command_macro(Arc::new(SimpleMacro::new(
            "emit-two",
            |_tail, span, _parser| {
                Ok(vec![
                    Command::PrintSize(span.clone(), None),
                    Command::PrintSize(span, Some("second".to_owned())),
                ])
            },
        )));
        let seed = capture(&mut parser, None, "(emit-two)\n(print-size)");

        assert_eq!(seed.groups.len(), 2);
        assert_eq!(seed.groups[0].subcommands.len(), 2);
        assert_eq!(seed.groups[1].subcommands.len(), 1);
        assert_eq!(
            seed.groups[0].subcommands[0].source,
            SourceSubcommandRef::new(SourceGroupId::new(0), SourceSubcommandId::new(0))
        );
        assert_eq!(
            seed.groups[0].subcommands[1].source,
            SourceSubcommandRef::new(SourceGroupId::new(0), SourceSubcommandId::new(1))
        );
        assert_eq!(
            seed.groups[1].subcommands[0].source,
            SourceSubcommandRef::new(SourceGroupId::new(1), SourceSubcommandId::new(0))
        );
    }

    #[test]
    fn zero_command_groups_and_comment_only_documents_are_retained() {
        let mut parser = Parser::default();
        parser.add_command_macro(Arc::new(SimpleMacro::new(
            "emit-none",
            |_tail, _span, _parser| Ok(Vec::new()),
        )));
        let seed = capture(&mut parser, None, "; before\n(emit-none)\n; after");
        assert_eq!(seed.groups.len(), 1);
        assert!(seed.groups[0].subcommands.is_empty());
        assert!(seed.document.groups[0].subcommands.is_empty());
        assert_eq!(
            &seed.document.contents[seed.document.eof_trailer.clone()],
            "\n; after"
        );

        let comments = capture(&mut Parser::default(), None, "; only\n; eof");
        assert!(comments.groups.is_empty());
        assert_eq!(
            comments.document.eof_trailer,
            0..comments.document.contents.len()
        );
    }

    #[test]
    fn repeated_capture_is_structurally_identical() {
        let input = "; lead\n(print-size)\n; eof";
        let first = capture(&mut Parser::default(), Some("same.egg".to_owned()), input);
        let second = capture(&mut Parser::default(), Some("same.egg".to_owned()), input);
        assert_eq!(first.document, second.document);
        assert_eq!(
            first
                .groups
                .iter()
                .flat_map(|group| group.subcommands.iter().map(|command| command.source))
                .collect::<Vec<_>>(),
            second
                .groups
                .iter()
                .flat_map(|group| group.subcommands.iter().map(|command| command.source))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn identity_conversion_fails_closed_at_u32_boundary() {
        let overflowing = usize::try_from(u64::from(u32::MAX) + 1).unwrap();
        assert_eq!(
            checked_group_id(overflowing),
            Err(FrontendSourceCaptureError::GroupIdentityExhausted {
                ordinal: overflowing
            })
        );
        assert_eq!(
            checked_subcommand_id(SourceGroupId::new(7), overflowing),
            Err(FrontendSourceCaptureError::SubcommandIdentityExhausted {
                group: SourceGroupId::new(7),
                ordinal: overflowing
            })
        );
    }
}
