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
    /// Whether this macro leaves a literal-free, closed constructor action
    /// unchanged. `None` identifies a union; `Some(head)` identifies an expression
    /// action whose outermost call has that name. The promise applies to actions
    /// whose calls pass ordinary parser precedence and declared-constructor type
    /// checks. This capability query must have no side effects and may be called
    /// before those checks complete.
    ///
    /// Opting in promises a singleton unchanged command, no error, and no side
    /// effects, so execution may skip `transform` for this action.
    fn preserves_closed_constructor_action(&self, _expression_head: Option<&str>) -> bool {
        false
    }

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

    pub(crate) fn preserves_closed_constructor_action(
        &self,
        expression_head: Option<&str>,
    ) -> bool {
        self.macros
            .iter()
            .all(|mac| mac.preserves_closed_constructor_action(expression_head))
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
}
