//! HYB-E6002: constant overflow against a declared fixed-width type.
//!
//! This check folds constant expressions appearing in initializers and
//! verifies that the resulting value fits the declared type. It must resolve
//! file-level `const` identifiers to their initializers so that aliases such
//! as `const big = 300; var n int8 = big` are rejected just like the literal
//! form `var n int8 = 300`.

use std::collections::HashMap;

use hyb_ast::{Expr, Item, Program, Stmt, Type};
use hyb_diagnostics::{Diagnostic, DiagnosticBag, Span};

/// A folded constant value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstValue {
    Int(i128),
}

/// Result of folding an expression: either a known constant value or a
/// non-constant expression (which we cannot reason about here).
type FoldResult = Option<ConstValue>;

/// File-level constant bindings, keyed by name.
///
/// Only file-level `const` items are recorded. Local bindings shadow these
/// names and must not be resolved through this map.
struct ConstEnv<'a> {
    bindings: HashMap<&'a str, &'a Expr>,
}

impl<'a> ConstEnv<'a> {
    fn collect(program: &'a Program) -> Self {
        let mut bindings = HashMap::new();
        for item in &program.items {
            if let Item::Const(c) = item {
                bindings.insert(c.name.as_str(), &c.value);
            }
        }
        Self { bindings }
    }

    fn lookup(&self, name: &str) -> Option<&'a Expr> {
        self.bindings.get(name).copied()
    }
}

/// Fold an expression to a constant value, resolving file-level const
/// identifiers to their initializers.
///
/// `locals` is the set of names bound by local declarations in the current
/// scope; identifiers in this set shadow file-level consts and are therefore
/// never resolved.
fn const_int_fold(
    expr: &Expr,
    env: &ConstEnv<'_>,
    locals: &[&str],
    depth: usize,
) -> FoldResult {
    // Guard against pathological / cyclic const chains.
    if depth > 64 {
        return None;
    }

    match expr {
        Expr::IntLit { value, .. } => Some(ConstValue::Int(*value)),
        Expr::Unary {
            op: hyb_ast::UnaryOp::Neg,
            operand,
            ..
        } => match const_int_fold(operand, env, locals, depth + 1)? {
            ConstValue::Int(v) => Some(ConstValue::Int(-v)),
        },
        Expr::Binary {
            op, lhs, rhs, ..
        } => {
            let l = const_int_fold(lhs, env, locals, depth + 1)?;
            let r = const_int_fold(rhs, env, locals, depth + 1)?;
            let (ConstValue::Int(a), ConstValue::Int(b)) = (l, r);
            let value = match op {
                hyb_ast::BinaryOp::Add => a.checked_add(b)?,
                hyb_ast::BinaryOp::Sub => a.checked_sub(b)?,
                hyb_ast::BinaryOp::Mul => a.checked_mul(b)?,
                hyb_ast::BinaryOp::Div => {
                    if b == 0 {
                        return None;
                    }
                    a.checked_div(b)?
                }
                hyb_ast::BinaryOp::Rem => {
                    if b == 0 {
                        return None;
                    }
                    a.checked_rem(b)?
                }
                _ => return None,
            };
            Some(ConstValue::Int(value))
        }
        Expr::Ident { name, .. } => {
            // A local binding shadows the file-level const.
            if locals.iter().any(|l| *l == name.as_str()) {
                return None;
            }
            let init = env.lookup(name)?;
            const_int_fold(init, env, locals, depth + 1)
        }
        _ => None,
    }
}

/// Return the inclusive integer range for a fixed-width integer type, if any.
fn int_range(ty: &Type) -> Option<(i128, i128)> {
    match ty {
        Type::Int8 => Some((i8::MIN as i128, i8::MAX as i128)),
        Type::Int16 => Some((i16::MIN as i128, i16::MAX as i128)),
        Type::Int32 => Some((i32::MIN as i128, i32::MAX as i128)),
        Type::Int64 => Some((i64::MIN as i128, i64::MAX as i128)),
        Type::Uint8 => Some((u8::MIN as i128, u8::MAX as i128)),
        Type::Uint16 => Some((u16::MIN as i128, u16::MAX as i128)),
        Type::Uint32 => Some((u32::MIN as i128, u32::MAX as i128)),
        Type::Uint64 => Some((u64::MIN as i128, u64::MAX as i128)),
        _ => None,
    }
}

/// Check a single initializer against a declared type.
fn check_initializer(
    declared: &Type,
    init: &Expr,
    env: &ConstEnv<'_>,
    locals: &[&str],
    span: Span,
    diags: &mut DiagnosticBag,
) {
    let Some((min, max)) = int_range(declared) else {
        return;
    };
    let Some(ConstValue::Int(value)) = const_int_fold(init, env, locals, 0) else {
        return;
    };
    if value < min || value > max {
        let name = match init {
            Expr::Ident { name, .. } => Some(name.as_str()),
            _ => None,
        };
        let type_name = type_display(declared);
        let message = match name {
            Some(n) => format!(
                "constant `{n}` overflows declared type `{type_name}` of `{}` (HYB-E6002)",
                current_binding_name(init).unwrap_or("<binding>")
            ),
            None => format!(
                "constant overflows declared type `{type_name}` (HYB-E6002)"
            ),
        };
        diags.push(Diagnostic::error("HYB-E6002", message, span));
    }
}

/// Best-effort recovery of the binding name for diagnostics. The caller
/// supplies the span of the initializer; the binding name is threaded through
/// by the caller in practice, but we keep this helper for the literal case.
fn current_binding_name(_init: &Expr) -> Option<&str> {
    None
}

fn type_display(ty: &Type) -> &'static str {
    match ty {
        Type::Int8 => "int8",
        Type::Int16 => "int16",
        Type::Int32 => "int32",
        Type::Int64 => "int64",
        Type::Uint8 => "uint8",
        Type::Uint16 => "uint16",
        Type::Uint32 => "uint32",
        Type::Uint64 => "uint64",
        _ => "<type>",
    }
}

/// Entry point: run the const-overflow check over a whole program.
pub fn check(program: &Program, diags: &mut DiagnosticBag) {
    let env = ConstEnv::collect(program);
    for item in &program.items {
        if let Item::Fn(f) = item {
            let mut locals: Vec<&str> = Vec::new();
            check_block(&f.body, &env, &mut locals, diags);
        }
    }
}

fn check_block(
    block: &hyb_ast::Block,
    env: &ConstEnv<'_>,
    locals: &mut Vec<&str>,
    diags: &mut DiagnosticBag,
) {
    for stmt in &block.stmts {
        match stmt {
            Stmt::VarDecl {
                name,
                ty,
                init,
                span,
            } => {
                if let (Some(ty), Some(init)) = (ty, init) {
                    check_initializer(ty, init, env, locals, *span, diags);
                }
                locals.push(name.as_str());
            }
            Stmt::ConstDecl { name, .. } => {
                locals.push(name.as_str());
            }
            Stmt::Expr { expr, .. } => {
                check_expr(expr, env, locals, diags);
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
                ..
            } => {
                check_expr(cond, env, locals, diags);
                let mut inner = locals.clone();
                check_block(then_block, env, &mut inner, diags);
                if let Some(eb) = else_block {
                    let mut inner = locals.clone();
                    check_block(eb, env, &mut inner, diags);
                }
            }
            Stmt::While { cond, body, .. } => {
                check_expr(cond, env, locals, diags);
                let mut inner = locals.clone();
                check_block(body, env, &mut inner, diags);
            }
            Stmt::Return { value, .. } => {
                if let Some(v) = value {
                    check_expr(v, env, locals, diags);
                }
            }
            _ => {}
        }
    }
}

fn check_expr(
    expr: &Expr,
    env: &ConstEnv<'_>,
    locals: &[&str],
    diags: &mut DiagnosticBag,
) {
    match expr {
        Expr::Binary { lhs, rhs, .. } => {
            check_expr(lhs, env, locals, diags);
            check_expr(rhs, env, locals, diags);
        }
        Expr::Unary { operand, .. } => check_expr(operand, env, locals, diags),
        Expr::Call { args, .. } => {
            for a in args {
                check_expr(a, env, locals, diags);
            }
        }
        _ => {}
    }
}
