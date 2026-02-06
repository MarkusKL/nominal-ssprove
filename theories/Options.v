From Stdlib Require Export Utf8.

#[export] Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Export all_ssreflect all_algebra reals distr realsum.

(* Enforce sensible proof structure. *)
#[export] Set Bullet Behavior "Strict Subproofs".
#[export] Set Default Goal Selector "!".
#[export] Set Primitive Projections.

From extructures Require Export ord fset fmap.
Export Num.Theory Order.POrderTheory.
From SSProve.Crypt Require Export NominalPrelude.
Export PackageNotation. #[global] Open Scope package_scope.
#[global] Open Scope ring_scope.
#[global] Open Scope sep_scope.
