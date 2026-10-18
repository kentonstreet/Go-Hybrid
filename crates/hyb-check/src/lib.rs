//! hyb-check: semantic checks for the Hy language.

pub mod checks;

use hyb_ast::Program;
use hyb_diagnostics::DiagnosticBag;

/// Run all semantic checks over a program.
pub fn check_program(program: &Program) -> DiagnosticBag {
    let mut diags = DiagnosticBag::new();
    checks::const_overflow::check(program, &mut diags);
    diags
}
