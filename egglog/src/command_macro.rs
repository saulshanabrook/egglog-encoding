//! Command-level macro system for egglog
//!
//! This module provides an API for external libraries to implement
//! command-level transformations, similar to procedural macros.

use crate::Error;
use crate::ast::*;
use crate::typechecking::TypeInfo;
use crate::util::SymbolGen;
use std::sync::Arc;

/// A command macro that can transform commands during desugaring
pub trait CommandMacro: Send + Sync {
    /// Transform the command, potentially using type information.
    /// Returns the transformed commands. If the macro doesn't apply,
    /// it should return vec![command] unchanged.
    fn transform(
        &self,
        command: Command,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error>;
}

/// A registry of command macros
#[derive(Default, Clone)]
pub struct CommandMacroRegistry {
    macros: Vec<Arc<dyn CommandMacro>>,
}

impl CommandMacroRegistry {
    /// Create a new empty registry
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a new command macro
    pub fn register(&mut self, macro_impl: Arc<dyn CommandMacro>) {
        self.macros.push(macro_impl);
    }

    /// Apply all registered macros to a command in sequence
    pub fn apply(
        &self,
        command: Command,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        // Start with the original command
        let mut commands = vec![command];

        // Apply each macro in sequence to all commands
        for macro_impl in &self.macros {
            let mut next_commands = Vec::new();
            for cmd in commands {
                next_commands.extend(macro_impl.transform(cmd, symbol_gen, type_info)?);
            }
            commands = next_commands;
        }

        Ok(commands)
    }

    /// Apply every registered macro while requiring each individual stage to
    /// preserve exactly one command.
    ///
    /// The standalone frontend can inherit one parsed source trigger through
    /// a one-to-one transformation. It cannot recover provenance after an
    /// intermediate fan-out or deletion, even if a later macro happens to
    /// collapse the final result back to one command. Ordinary execution keeps
    /// using [`Self::apply`] and retains the public macro API's zero/many-output
    /// semantics.
    pub(crate) fn apply_one_to_one_for_standalone(
        &self,
        command: Command,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Command, Error> {
        let mut command = command;
        for macro_impl in &self.macros {
            let mut transformed = macro_impl.transform(command, symbol_gen, type_info)?;
            if transformed.len() != 1 {
                let message = if transformed.is_empty() {
                    "zero-output command-macro expansion lacks standalone provenance"
                } else {
                    "multi-output command-macro expansion lacks standalone provenance"
                };
                return Err(Error::StandaloneSnapshotInvariant { message });
            }
            command = transformed.pop().unwrap();
        }
        Ok(command)
    }
}
