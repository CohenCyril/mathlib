/-
Copyright (c) 2016 Cyril Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
author: Cyril Cohen <cyril.cohen@inria.fr>
with contributions and help from Robert Y. Lewis <rob.y.lewis@gmail.com>
and Johannes Hölzl <johannes.hoelzl@gmx.de>

Binary parametricity translation (WIP)

the translation is adapted from
/Parametricity in an Impredicative Sort/
by Chantal Keller and Marc Lasson
in Computer Science Logic 2012 (CSL’12).
-/

import tactic tactic.find
import logic.relation
import category.monad.basic category.monad.writer
open expr native tactic
open lean.parser interactive
set_option pp.universes true

universes u u' v v' l l' w uu

meta def expr.instantiate_lam (nv : expr) : expr → expr
| (lam nm bi tp bd) := bd.instantiate_var nv
| e := mk_app e [nv]

meta def expr.mk_subst_or_app : expr → list expr → expr
| e []      := e
| e (x::xs) := (x.instantiate_lam e).mk_subst_or_app xs

private def bid := binder_info.default

meta def expr.strip_lam : expr → nat → option expr
| (lam _ _ _ bd) (nat.succ n) := bd.strip_lam n
| t 0 := return t
| _ _ := none

meta def concl : expr → expr | (pi _ _ _ ty) := concl ty | ty := ty
meta def hdapp : expr → expr | (app x _)     := hdapp x  | x := x
meta def slevel : expr → level | (sort lvl) := lvl | _ := level.zero
meta def lparam : level → name | (level.param n) := n | _ := ""

meta def expr.collect_const : expr → list name
| (const a a_1) := [a]
| (mvar a a_1 a_2) := a_2.collect_const
| (local_const a a_1 a_2 a_3) := a_3.collect_const
| (app a a_1) := a.collect_const.union a_1.collect_const
| (lam a a_1 a_2 a_3) := a_2.collect_const.union a_3.collect_const
| (pi a a_1 a_2 a_3) := a_2.collect_const.union a_3.collect_const
| (elet a a_1 a_2 a_3) :=
    a_1.collect_const.union $ a_2.collect_const.union a_3.collect_const
| (macro a a_1) := (a_1.map expr.collect_const).join
| e@(var a) := []
| e@(sort a) := []

--
meta def split_pis : option ℕ → expr → list expr × expr
| (some 0) ty := ([], ty)
| n (pi _ _ α ty) :=
  let (αs, ty) := split_pis ((λ x : ℕ, x - 1) <$> n) ty in
  (α :: αs, ty)
| _ ty := ([], ty)

inductive test : Type (max (v+1) v u)
| zero : test
| one (t : forall x : Type v, list x -> Sort u): test
#check (forall test : Type w, forall x : Type v, list x -> Sort u -> test)
#print test

structure is_fun {α : Sort u} {β : Sort v} (R : α → β → Sort w) :=
  (f : α → β) (fR : Π a, R a (f a))
  (Rf : ∀ a b, R a b -> b = f a)

structure is_iso {α : Sort u} {β : Sort v} (R : α → β → Sort w) :=
  (direct : is_fun R) (reverse : is_fun (flip R))

structure eq_rel (α : Sort u) (β : Sort v) :=
  (rel : α → β → Sort w) (iso : is_iso rel)

def eq_rel_eq_rel : eq_rel (Type u) (Type u) := begin
  refine ⟨eq_rel,
    ⟨⟨id, λ a, ⟨λ a b, a = b, ⟨⟨id, λ _, rfl, λ _ _, eq.symm⟩,
                               ⟨id, λ _, rfl, λ _ _, id⟩⟩⟩, sorry⟩,
     ⟨id, λ a, ⟨λ a b, a = b, ⟨⟨id, λ _, rfl, λ _ _, eq.symm⟩,
                               ⟨id, λ _, rfl, λ _ _, id⟩⟩⟩, sorry⟩⟩
  ⟩
  end

lemma eq_rel_prop_equiv (P1 P2 : Prop) :
  (eq_rel P1 P2 → (P1 ↔ P2)) := begin
{rintros ⟨R,⟨⟨f,fR⟩,⟨g,gR⟩⟩⟩, split, {exact f}, {exact g}}
end

lemma prop_equiv_eq_rel (P1 P2 : Prop) :
  ((P1 ↔ P2) → eq_rel.{0 0 0} P1 P2) := begin
{rintros ⟨f,g⟩,
 refine ⟨λ p q, f p = q, ⟨⟨f, λ a, rfl, sorry⟩,⟨g, λ b, rfl, sorry⟩⟩⟩}
end

set_option pp.all false
set_option trace.check true
lemma pi_eq_rel (α0 α1 : Sort u) (αR : eq_rel.{u u w} α0 α1) 
  (β0 : α0 → Sort v) (β1 : α1 → Sort v)
  (βR : ∀ (a0 : α0) (a1 : α1) (aR : αR.rel a0 a1),
    eq_rel.{v v l} (β0 a0) (β1 a1)) :
  eq_rel.{_ _ (imax u u w l)} (Π a0, β0 a0) (Π a1, β1 a1) := begin
  refine ⟨λ (f0 : Π a0, β0 a0) (f1 : Π a1, β1 a1),
            Π (a0 : α0) (a1 : α1) (aR : αR.rel a0 a1),
             (βR a0 a1 aR).rel (f0 a0) (f1 a1)
  ,⟨⟨λ f0 a1, (βR _ _ $ αR.iso.reverse.fR a1).iso.direct.f (f0 _),_, _⟩
   ,⟨λ g0 a0, (βR _ _ $ αR.iso.direct.fR a0).iso.reverse.f (g0 _),_, _⟩⟩⟩, {
    rintros f0 a0 a1 aR,
    have β := (βR a0 a1 aR).iso.direct.fR (f0 a0),

    have := αR.iso.reverse.Rf _ _ aR,
    induction this,

    have := (βR _ _ _).iso.reverse.Rf _ _ (this _), {
      rw [this],
    }

  },

    end
#print pi_eq_rel


meta def expr.skeleton : expr → tactic pexpr
| (var a) := return $ var a
| (sort a) := sort <$> mk_meta_univ
| (const a a_1) := return $ const a []
| p@(mvar a a_1 a_2) := mvar a a_1 <$> (infer_type p >>= expr.skeleton)
| p@(local_const a a_1 a_2 a_3) := local_const a a_1 a_2 <$> (infer_type p >>= expr.skeleton)
| (app a a_1) := app <$> (pexpr.mk_explicit <$> expr.skeleton a) <*> expr.skeleton a_1
| (lam a a_1 a_2 a_3) := lam a a_1 <$> a_2.skeleton <*> a_3.skeleton
| (pi a a_1 a_2 a_3) := pi a a_1 <$> a_2.skeleton <*> a_3.skeleton
| (elet a a_1 a_2 a_3) := elet a <$> a_1.skeleton <*> a_2.skeleton <*> a_3.skeleton
| (macro a a_1) := macro a <$> a_1.mmap expr.skeleton

meta def name.ext (ext : string) (x : name) : name :=
  (x.to_string ++ ext : string)

meta def param.fresh (lconsts : name_map (expr × expr × expr))
    (x : name) (α0 α1 αR : expr) :
  tactic ((expr × expr × expr) × name_map (expr × expr × expr)) := do
  uniq_name0 ← mk_fresh_name,
  let fresh0 := expr.local_const uniq_name0 (x.ext "0") bid α0,
  fresh1 ← mk_local_def (x.ext "1") α1,
  freshR ← mk_local_def (x.ext "R") (αR.mk_subst_or_app [fresh0, fresh1]),
  let freshs := (fresh0, fresh1, freshR),
  return (freshs, lconsts.insert uniq_name0 freshs)

meta def param.intro (lconsts : name_map (expr × expr × expr))
    (x : name) (α0 α1 αR : expr) (body : expr) :
      tactic ((expr × expr × expr) × name_map (expr × expr × expr) × expr) := do
  (fs@(f0, f1, fR), lconsts) ← param.fresh lconsts x α0 α1 αR,
  return (fs, lconsts, body.instantiate_var f0)

meta def name.param (n : nat) (x : name) : name :=
  x ++ "param" ++ to_string n

meta def environment.trailing_pi_type_of (env : environment) : expr → option name
 | (pi _ _ t b) := match b with
   | (pi _ _ _ _) := environment.trailing_pi_type_of b
   | _ := some t.get_app_fn.const_name
   end
 | _ := none

meta def environment.inductive_type_of_rec (env : environment) (n : name) : option name :=
  match env.get n with
  | (exceptional.success decl) := env.trailing_pi_type_of decl.type
  | _ := none
  end

meta def expr.param' (current : expr := mk_true)
  (p : nat) (umap : name_map name) : expr →
  name_map (expr × expr × expr) →
  tactic (expr × expr × expr)
| (var         db) _ := fail $ "expr.param: cannot translate a var"
| exp@(sort        lvl) _ := do
  trace $ "expr.param' " ++ to_string exp,
  let lvl1 := lvl.instantiate (umap.map $ level.param).to_list,
  lvlR ← mk_meta_univ,
  return (sort lvl, sort lvl1,
    lam "α0" bid (sort lvl) $ lam "α1" bid (sort lvl1) $
    pi "x0" bid (var 1) $ pi "x1" bid (var 1) $ sort lvlR)
| c@(const       x lvls) _ := do
    trace $ "expr.param' " ++ to_string c,
    let xR := x.param p,
    let lvls1 := lvls.map (λ lvl, lvl.instantiate (umap.map $ level.param).to_list),
    if xR = current.local_pp_name then return (c, const x lvls1, current) else do
    env ← get_env,
    if ¬ env.contains xR
    then fail $ "expr.param': const " ++ to_string xR ++ "unknown"
    else do
    xR_decl ← env.get xR,
    /- do env ← get_env, env.get xR, /- fix: test only non current definitions -/ -/
    lvlsR ← mk_num_meta_univs $ (xR_decl.univ_params.length - 2 * lvls.length),
    return (c, const x lvls1, const xR (lvls ++ lvls1 ++ lvlsR))
| c@(local_const x pry binfo α) lconsts := do
    trace $ "expr.param' " ++ to_string c,
    match lconsts.find x with
   | some c01R := return c01R
   | none := fail ("expr.param': local_const " ++ to_string x ++ " not found")
   end
| exp@(app u v) lconsts := do
    trace $ "expr.param' " ++ to_string exp,
  (u0, u1, uR) ← u.param' lconsts,
  (v0, v1, vR) ← v.param' lconsts, /- trace $ "u = " ++ to_string u ++ ";   uR = " ++ to_string uR, -/
  return (mk_app u0 [v0], mk_app u1 [v1], mk_app uR [v0, v1, vR])
| exp@(lam x binfo α body) lconsts := do
  trace $ "expr.param' " ++ to_string exp,
  (α0, α1, αR) ← α.param' lconsts,
  ((x0, x1, xR), lconsts, body) ← param.intro lconsts x α0 α1 αR body,
  (body0, body1, bodyR) ← body.param' lconsts,
  let t0 := body0.mk_binding lam x0,
  let t1 := body1.mk_binding lam x1,
  let tR := ((bodyR.mk_binding lam xR).mk_binding lam x1).mk_binding lam x0,
  return (t0, t1, tR)
| exp@(pi x binfo α body) lconsts := do
  trace $ "expr.param' " ++ to_string exp,
  (α0, α1, αR) ← α.param' lconsts,
  ((x0, x1, xR), lconsts, body) ← param.intro lconsts x α0 α1 αR body,
  (body0, body1, bodyR) ← body.param' lconsts,
  let t0 := body0.mk_binding pi x0,
  let t1 := body1.mk_binding pi x1,
  f0 ← mk_local_def "f0" t0,
  f1 ← mk_local_def "f1" t1,
  let tR := (((((bodyR.mk_subst_or_app [f0 x0, f1 x1]
     ).mk_binding pi xR).mk_binding pi x1).mk_binding pi x0
     ).mk_binding lam f1).mk_binding lam f0,
  return (t0, t1, tR)
| exp@(elet  x α val body) lconsts := do
  trace $ "expr.param' " ++ to_string exp,
  (α0, α1, αR) ← α.param' lconsts,
  (val0, val1, valR) ← val.param' lconsts,
  ((x0, x1, xR), lconstss, body) ← param.intro lconsts x α0 α1 αR body,
  (body0, body1, bodyR) ← body.param' lconstss,
  let let0 x (_ : binder_info) ty := elet x ty val0,
  let let1 x (_ : binder_info) ty := elet x ty val1,
  let letR x (_ : binder_info) ty := elet x ty valR,
  let t0 := body0.mk_binding let0 x0,
  let t1 := body1.mk_binding let1 x1,
  let tR := ((bodyR.mk_binding letR xR).mk_binding let1 x1).mk_binding let0 x0,
  return (t0, t1, tR)
| exp lconsts := do
  trace $ "expr.param' " ++ to_string exp,
  match exp.is_sorry with
  | some α := do
    (α0, α1, αR) ← α.param' lconsts,
    return (mk_sorry α0, mk_sorry α1, (mk_sorry αR).mk_subst_or_app [mk_sorry α0, mk_sorry α1])
  | none := fail $
    "expr.param': expression " ++ exp.to_string ++ " is not translatable"
  end

meta def expr.param (t : expr) (current : expr := var 0) (p := 2)
    (umap : name_map name) (lconst : name_map _) :=
  expr.param' current p umap t lconst

meta def param.fresh_from_pis (p := 2) (umap  : _):
      name_map (expr × expr × expr) → option ℕ → expr →
    tactic ((list expr × list expr × list expr) × name_map (expr × expr × expr) × expr)
  | lconsts (some nat.zero) ty := return (([], [], []), lconsts, ty)
  | lconsts n (pi x binfo α body) := do
      let n := (λ x : ℕ, x - 1) <$> n,
      (α0, α1, αR) ← α.param mk_true p umap lconsts,
      ((f0, f1, fR), lconsts, ty') ← param.intro lconsts x α0 α1 αR body,
      /- trace ("param.fresh_from_pis recursive call", n), -/
      ((fs0, fs1, fsR), lconsts, rest) ← param.fresh_from_pis lconsts n ty',
      return ((f0 :: fs0, f1 :: fs1, fR :: fsR), lconsts, rest)
  | _ _ _ := fail $ "param.fresh_from_pi: not enough pi"


meta def param.entangle : (list expr × list expr × list expr) → list expr
| (x :: xs, y :: ys, z :: zs) := x :: y :: z :: param.entangle (xs, ys, zs)
| _ := []

meta def expr.mk_bindings (k : name → binder_info → expr → expr → expr)
  (vars : list expr) (e : expr) : expr := vars.foldr (mk_binding k) e

#print declaration

#print nat.pred._main
#print nat.cases_on
#help commands

-- #set_option profiler true

 -- #eval nat.pred 10000
#eval to_string $ level.normalize $
  level.succ (level.max (level.succ (level.mvar "u")) (level.succ (level.mvar "v")))

inductive propind : Prop
| dummy : propind
| zero (α : Type u → propind) : propind

#print propind
-- #run_cmd do
--   let n := `(nat.pred 10),
--   nfn ← tactic.whnf n,
--   trace n
meta def level.parametrize : level → level
| (level.succ l)     := level.succ l.parametrize
| (level.max l1 l2)  := level.max l1.parametrize l2.parametrize
| (level.imax l1 l2) := level.imax l1.parametrize l2.parametrize
| (level.mvar  n)    := level.param n
| e                  := e

meta def expr.uparametrize : expr → expr
| (sort l) := sort l.parametrize
| (const n ls) := const n $ ls.map (level.parametrize)
| (mvar n m t) := mvar n m t.uparametrize
| (local_const n m bi t) := local_const n m bi t.uparametrize
| (app e f) := app e.uparametrize f.uparametrize
| (lam n bi e t) := lam n bi e.uparametrize t.uparametrize
| (pi n bi e t) := pi n bi e.uparametrize t.uparametrize
| (elet n g e f) :=
   elet n g.uparametrize e.uparametrize f.uparametrize
| (macro d args) := macro d $ args.map expr.uparametrize
| e@(var n) := e

meta def expr.delta_to_main (e : expr) : tactic expr := do
  env ← get_env,
  let ns := e.collect_const,
  flip delta e $
  ns.foldr (λ n ns,
   if env.contains (n ++ `_main) ∨ (env.is_projection n).is_some
   then n :: ns else ns) []

meta def dunify (e1 e2 : expr) : tactic unit := do
    e1 ← e1.delta_to_main <|> pure e1,
    e2 ← e2.delta_to_main <|> pure e2,
    trace $ "dunify " ++ to_string e1
               ++ " with " ++ to_string e2,
    unify e1 e2 transparency.all
/-
meta def is_sort (e : expr) : tactic level := do
  l ← mk_meta_univ,
  unify e (sort l) transparency.all,
  get_univ_assignment l

meta def mk_meta : tactic expr := do
  fresh_sort ← @sort tt <$> mk_meta_univ,
  mk_meta_var fresh_sort

meta def expr.infer_type : expr → tactic expr
| (app e f) := do
    e_ty ← e.infer_type, f_ty ← f.infer_type,
    e_ret_ty ← mk_meta,
    unify e_ty (pi `_ bid f_ty e_ret_ty) transparency.all,
    return (e_ret_ty.instantiate_var f)

| (lam n bi e t) := do
  x ← mk_local' n bi e, let tx := t.instantiate_var x,
  tx_ty ← tx.infer_type,
  e_ty ← e.infer_type, is_sort e_ty,
  return (tx_ty.mk_binding pi x)

| (pi n bi e t) := do
  le ← e.infer_type >>= is_sort,
  lt ← t.infer_type >>= is_sort,
  return (sort (level.imax le lt))

| (elet n g e f) := do
  e_ty ← e.infer_type, is_sort e_ty,
  g_ty ← g.infer_type,
  unify g_ty e transparency.all,
  (f.instantiate_var g).infer_type

| (macro d args) := fail $ "infer: cannot handle macros"
| e@(local_const n m bi t) := return t
| e@(mvar n m t) := return t
| e@(sort l) := return $ sort (level.succ l)
| e@(const n ls) := infer_type e
| e@(var n) := fail $ "infer: cannot check (de Brujin) open terms"
 -/

meta def expr.elab (e : expr) : tactic expr := do
  env ← get_env,
  trace $ "e = " ++ to_string (to_raw_fmt e), trace "",
  p ← e.skeleton,
  trace $ "p = " ++ to_string (to_raw_fmt p), trace "",
  e' ← to_expr p,
  trace $ "e' = " ++ to_string (to_raw_fmt e'),  trace "",
  dunify e' e,
  e ← instantiate_mvars e,
  trace $ "unified e = " ++ to_string (to_raw_fmt e), trace "",
/-   e.infer_type,
  e ← instantiate_mvars e, -/
  return e

meta def elaborate_definition (univs01 : list name)
 (ty : expr) (term : expr) : tactic (list name × expr × expr) :=
do
  ty ← ty.elab,
  term ← term.elab,
  tty ← infer_type term,
  dunify tty ty,
  pty ← expr.uparametrize <$> instantiate_mvars ty,
  pterm ← expr.uparametrize <$> instantiate_mvars term,
  let all_univs := pty.collect_univ_params.union pterm.collect_univ_params,
  return (all_univs.remove_all univs01, pty, pterm)

meta def expr.lconstify (fn cn : name) (ty : expr) : expr → expr
| e@(const n ls) := if n = cn then local_const fn cn binder_info.default ty else e
| (mvar n m t) := mvar n m t.lconstify
| (local_const n m bi t) := local_const n m bi t.lconstify
| (app e f) := mk_app e.lconstify [f.lconstify]
| (lam n bi e t) := lam n bi e.lconstify t.lconstify
| (pi n bi e t) := pi n bi e.lconstify t.lconstify
| (elet n g e f) := elet n g.lconstify e.lconstify f.lconstify
| (macro d args) := macro d $ args.map expr.lconstify
| e := e

meta def expr.constify (fn cn : name) (lvls : list level) (e : expr) : expr :=
  instantiate_local fn (const cn lvls) e

/-
  let lam_xs := const (`punit ++ `star) [level.zero]).mk_bindings lam xs
  infer_type ()
  >>= unify ((const `punit [level.zero]).mk_bindings pi ts),
  trace $ "typeckecking: " ++ to_string iargs ++ " wrt " ++ to_string iparams, -/



meta def tele_check : list expr → list expr → tactic unit
| (e :: es) (x :: ts) := do
  trace $ "tele_check: " ++ to_string e ++ " : " ++ to_string (local_type x),
  infer_type e >>= dunify (local_type x),
  tele_check es (ts.map (λ y, instantiate_local (local_uniq_name x) e y))
| _ _ := return punit.star

meta def elab_ctor (x : expr) (e : expr) : tactic expr := do
  trace $ "elab_ctor input:" ++ to_string e,
  (cparams, concl) ← mk_local_pis e,
  (iparams, _) ← mk_local_pis (local_type x),
  let iargs := get_app_args concl,
  tele_check iargs iparams,
   e ← instantiate_mvars e,
  trace $ "elab_ctor output = " ++ to_string e,
   return e

meta def elaborate_inductive (x : expr) (univs01 : list name) (p : name)
 (ty : expr) (ctors : list expr) : tactic (list name × expr × list expr) :=
do
  let pty0 := ty.instantiate_univ_params [(p, level.zero)],
  trace $ "elaborate_inductive: expr.elab",
  elctors ← ctors.mmap (elab_ctor x),
  trace $ "elaborate_inductive: begin uparam",
  let plctors := elctors.map (λ elctor,
    elctor.uparametrize.instantiate_univ_params [(p, level.zero)]),
  trace $ "elaborate_inductive: univ normalizing",
  ctypes ← plctors.mmap infer_type,
  trace $ "ctypes = " ++ to_string ctypes,
  clvls ← plctors.mmap (λ plctor, level.normalize <$> slevel <$> infer_type plctor),
  trace $ "clvls = " ++ to_string clvls,
  trace $ "elaborate_inductive: computing indlvl",
  let indlvl := level.succ (clvls.foldr level.max level.zero).normalize,
  trace $ "indlvl = " ++ to_string indlvl,
  trace $ "ty = " ++ to_string ty,
  trace $ "pty0 = " ++ to_string pty0,/-
  let ptyu := if ctors.length ≤ 1 then pty0 else
    ty.instantiate_univ_params [(p, indlvl)],
  trace $ "ptyu = " ++ to_string ptyu, -/
  let all_univs := plctors.foldr
    (λ e univs, list.union univs e.collect_univ_params) [],
  let univsR := all_univs.remove_all univs01,
  let ectors := plctors.map (λ lctor,
    lctor.constify (x.local_uniq_name) (x.local_pp_name)
      ((univs01 ++ univsR).map (λ u, level.param u))
  ),
  return (univsR, pty0, ectors)

meta def param.recursor (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  ind_decl ← get_decl n,
  guard $ env.is_inductive n,
  let ctors := env.constructors_of n,
  let nparams := env.inductive_num_params n,
  let nindices := env.inductive_num_indices n,
  trace ("ctors = ", ctors),
  let rec_name : name := n ++ "rec",
  trace ("rec_name = ", rec_name),
  let Rrec_name : name := n.param p ++ "rec",
  rec_decl ← get_decl rec_name,
  let rec_ty := rec_decl.type,
  trace ("rec_ty = ", rec_ty),
  let univs := rec_decl.univ_params,
  let lvls := univs.map level.param,
  trace ("lvls = ", lvls),
  univs1 ← univs.mmap (λ _, mk_fresh_name),
  let umap := rb_map.of_list (univs.zip univs1),
  let lvls1 := univs1.map level.param,
  let rec : expr := const rec_name lvls,
  let rec1 : expr := const rec_name lvls1,/-
  let Rrec : expr := const Rrec_name (lvls ++ lvls1), -/
  trace ("rec:", rec),
  (rec_ty0, rec_ty1, rec_tyR) ← rec_ty.param mk_true p umap mk_name_map,
  let rec_tyRrr := rec_tyR.mk_subst_or_app [rec, rec1],
  trace ("rec_tyRrr:", rec_tyRrr),/-
  (params@(params0, params1, paramsR), lconsts, rec_ty_no_params) ←
    param.fresh_from_pis p umap mk_name_map (some nparams) rec_ty,
  trace ("params:", params),
  (pred@([pred0], [pred1], [predR]), lconsts, rec_ty_ctors) ←
    param.fresh_from_pis p umap lconsts (some 1) rec_ty_no_params,
  trace ("pred:", pred),
  (cases@(cases0, cases1, casesR), lconsts, rec_ty_indices) ←
    param.fresh_from_pis p umap lconsts (some ctors.length) rec_ty_ctors,
  trace ("cases:", cases),
  (indices@(indices0, indices1, indicesR), lconsts, rec_ty_ind) ←
    param.fresh_from_pis p umap lconsts (some nindices) rec_ty_indices,
  trace ("indices:", indices),
  (ind@([ind0], [ind1], [indR]), lconsts, rec_ty_stripped) ←
    param.fresh_from_pis p umap lconsts (some 1) rec_ty_ind,
  trace ("ind:", ind),
  trace ("lconsts:", lconsts),
  (_, _, PntR) ← (pred0.mk_app (indices0 ++ [ind0])).param p umap lconsts,
  trace ("PntR:", PntR),
  Rcases ← (list.zip ctors cases0).mmap (λ ⟨n, e⟩, do
    decl ← get_decl n,
    let ctor_ty := decl.type,
    (params@(params0, params1, paramsR), lconsts, ctor_ty_noparams) ←
      param.fresh_from_pis p umap mk_name_map (some nparams) ctor_ty,
    (args@(args0, args1, argsR), lconsts, ctor_ret_ty) ←
      param.fresh_from_pis p umap lconsts none ctor_ty_noparams,
    (_, _, ebuR) ← (mk_app e $ params0 ++ args0).param p umap lconsts,
    let recargs := args0.filter (λ a, n = (const_name $ hdapp $ concl $ local_type a)),
    rec01args ← recargs.mfoldr (λ a v, do
      rec0 ← mk_mvar, rec1 ← mk_mvar,
      return $ rec0 :: rec1 :: v
    ) [],
    return $ expr.mk_bindings lam (param.entangle params ++ param.entangle args)
      (mk_app ebuR rec01args)
  ),
  trace ("Rcases:", Rcases),
  let PntRrr := PntR.mk_subst_or_app
   [rec.mk_app (params0 ++ [pred0] ++ cases0 ++ indices0 ++ [ind0]),
   rec1.mk_app (params1 ++ [pred1] ++ cases1 ++ indices1 ++ [ind1])],
  trace ("PntRrr:", PntR),
  let rec_bodyR := Rrec.mk_app $ (param.entangle params) ++
    [expr.mk_bindings lam (param.entangle indices ++ [ind0, ind1, indR]) PntRrr],
  trace ("rec_bodyR", PntR),
  let recR := expr.mk_bindings lam
   (param.entangle params ++ param.entangle pred ++ param.entangle cases) rec_bodyR,
  trace ("recR:", recR), -/
  /- infer_type recR >>= λ btyR, unify rec_tyRrr btyR transparency.all,
  recR_unif ← instantiate_mvars recR,
  trace ("recR_unif:", recR_unif), -/
  rec_tyRrr ← rec_tyRrr.elab,
  let rec_tyRrr := rec_tyRrr.uparametrize,
  trace ("uparametrized rec_tyRrr = ", rec_tyRrr),
  let univsR := rec_tyRrr.collect_univ_params.remove_all (univs ++ univs1),
  add_decl $ mk_definition ((n ++ "rec").param 2)
    (univs ++ univs1 ++ univsR) rec_tyRrr rec_tyRrr.mk_sorry

meta def param.inductive (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  ind_decl ← get_decl n,
  guard $ env.is_inductive n,
  let ctors := env.constructors_of n,
  let nparams := env.inductive_num_params n,
  let nindices := env.inductive_num_indices n,
  let univs := ind_decl.univ_params,
  univs1 ← univs.mmap (λ _, mk_fresh_name),
  let umap := rb_map.of_list (univs.zip univs1),
  let lvls := univs.map level.param,
  let lvls1 := univs1.map level.param,
  let ty := ind_decl.type,
  let nR := n.param p,
  (ty0, ty1, tyR) ← ty.param mk_true p umap mk_name_map,
  trace $ ("tyR", to_string tyR),
  let tyRii := tyR.mk_subst_or_app [const n lvls, const n lvls1],
  tyRii ← tyRii.elab,
  let tyRii := tyRii.uparametrize,
  let uty := lparam $ slevel $ concl tyRii,
  trace $ "return type universe = " ++ to_string uty,
  cn ← mk_local_def nR tyRii,
  trace $ ("tyRii", to_string tyRii),
  trace ("lvls", lvls),
  trace ("ctors:", ctors),
  ctorsR ← ctors.mmap (λ (n : name), do
    decl ← get_decl n,
    let ty := decl.type,
    trace $ "param ctor " ++ to_string n,
    (ty0, ty1, tyR) ← ty.param cn p umap mk_name_map,
    let tyRcc := tyR.mk_subst_or_app [const n lvls, const n lvls1],
    return (n.param p, tyRcc)),
  let (cnamesR, ctysR) := ctorsR.unzip,
  trace ("=========== elaborating inductive ============="),
  (univsR, tyRii, ctysR) ← elaborate_inductive cn (univs ++ univs1) uty tyRii ctysR,
  let ctorsR := list.zip cnamesR ctysR,
  trace $ ("ctorsR:", to_string ctorsR),
  trace ("=========== adding inductive ============="),
  trace $ "universes " ++ (univs ++ univs1 ++ univsR).foldr (λ u s, to_string u ++ " " ++ s) "",
  trace $ "inductive " ++ to_string (n.param p) ++ " : " ++ to_string tyRii,
  ctorsR.mmap' (λ ⟨n, ty⟩, trace $ "| " ++ to_string n ++ " : " ++ to_string ty),
  add_inductive (n.param p) (univs ++ univs1 ++ univsR) ((p + 1) * nparams) tyRii ctorsR,
  trace ("=========== inductive added ============="),
  param.recursor p n


meta def param.axiom (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  if env.contains (n.param p)
    then return ()
  else do
  decl ← env.get n,
  let univs := decl.univ_params,
  let α := decl.type,
  univs1 ← univs.mmap (λ _, mk_fresh_name),
  let umap := rb_map.of_list (univs.zip univs1),
  let (lvls, lvls1) := (univs.map level.param, univs1.map level.param),
  trace ("def type:", α),
  (_, _, αR) ← α.param mk_true 2 umap mk_name_map,
  let tyRrr := αR.mk_subst_or_app [const n lvls, const n lvls1],
  trace ("def tyR:", tyRrr),
  tyRrr ← tyRrr.elab,
  let tyRrr := tyRrr.uparametrize,
  trace ("uparametrized tyRrr:", tyRrr),
  let univsR := tyRrr.collect_univ_params.remove_all (univs ++ univs1),
  add_decl $ mk_definition (n.param 2)
    (univs ++ univs1 ++ univsR) tyRrr tyRrr.mk_sorry

meta def param.def (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  guard $ env.is_definition n,
  decl ← env.get n,
  match decl with
  | (declaration.defn _ univs α body _ _) := do
    univs1 ← univs.mmap (λ _, mk_fresh_name),
    let umap := rb_map.of_list (univs.zip univs1),
    let (lvls, lvls1) := (univs.map level.param, univs1.map level.param),
    let α := env.unfold_all_macros α,
    trace ("def type = ", α),
    trace $ ("def body with macro = ", to_string body),
    let body := env.unfold_all_macros body,
    trace $ ("def body = ", body.to_raw_fmt),
    (_, _, αR) ← α.param mk_true 2 umap mk_name_map,
    trace ("def αR = ", αR),
    let tyR := αR.mk_subst_or_app [const n lvls, const n lvls1],
    trace ("def tyR = ", tyR),
    /- trace ("def αR:", αR), -/
    (_, _, bodyR) ← body.param mk_true 2 umap mk_name_map,
    trace ("def bodyR = ", bodyR.to_raw_fmt),
    /- btyR ← infer_type bodyR, -/
    /- unify tyR btyR transparency.all,
    tyR_unif ← instantiate_mvars tyR,
    trace ("def tyR_unif:", tyR_unif), -/
    /- trace ("def tyR_unif:", tyR_unif.to_raw_fmt), -/
    trace ("============ elaborate definition ============="),
    (univsR, tyR, bodyR) ← elaborate_definition (univs ++ univs1) tyR bodyR,
    trace ("============ adding definition ============="),
    trace $ "def " ++ to_string (n.param 2) ++ " : " ++ to_string tyR ++ " :=",
    trace $ bodyR,
    add_decl $ mk_definition (n.param 2) (univs ++ univs1 ++ univsR) tyR bodyR,
    trace ("============ added definition =============")
  | _ := fail $ "param.def:  not a definition"
  end

meta def param.decl (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  if env.contains (n.param p)
    then return ()
  else if ¬ env.contains n
     then fail $ "param.decl: " ++ to_string n ++ " not in env"
  else do
  if env.is_inductive n then param.inductive p n
  else if env.is_definition n then param.def p n
  else fail $ "translate: cannot translate " ++ to_string n

meta def declaration.collect_const : declaration → list name
| (declaration.defn n ls t v h tr) := t.collect_const.union v.collect_const
| (declaration.thm n ls t v)       := t.collect_const.union v.get.collect_const
| (declaration.cnst n ls t tr)     := t.collect_const
| (declaration.ax n ls t)          := t.collect_const

meta def param.decl_rec (p := 2) (ax := ff) : name → tactic unit := λ n, do
  env ← get_env,
  if ¬ env.contains n
     then fail $ "param.decl: " ++ to_string n ++ " not in env"
  else do
  d ← env.get n,
  let deps := d.collect_const,
  deps.mmap param.decl_rec,
  param.decl p n <|> if ax then param.axiom p n
    else fail $ "cannot translate " ++ to_string n

@[user_command]
meta def param_cmd (_ : parse $ tk "#param") : lean.parser unit := do
  ns ← many ident,
  of_tactic $ ns.mmap' (param.decl 2)

@[user_command]
meta def param_axiom_cmd (_ : parse $ tk "#param_axiom") : lean.parser unit := do
  ns ← many ident,
  of_tactic $ ns.mmap' (param.axiom 2)

@[user_command]
meta def param_rec_cmd (_ : parse $ tk "#param_rec") : lean.parser unit := do
  ns ← many ident,
  of_tactic $ ns.mmap' (param.decl_rec 2)

@[user_command]
meta def param_rec_ax_cmd (_ : parse $ tk "#param_rec_ax") : lean.parser unit := do
  ns ← many ident,
  of_tactic $ ns.mmap' (param.decl_rec 2 tt)
----------------------
-- Working examples --
----------------------

#param_rec empty nonempty punit bool list nat or and not
#param_rec has_zero has_one has_neg has_add has_mul
#param_rec id

def n_id : ℕ → ℕ
| nat.zero := nat.zero
| (nat.succ k) := nat.succ k

def n_id2 := n_id._main
#print n_id -- n_id._main
#print n_id2 -- n_id._main

set_option pp.all false

structure box_nat := (unbox : nat)

#param box_nat
#param box_nat.unbox

#print pprod.fst


#param_rec n_id
#param_rec pprod.fst
#param_rec pprod.snd
#param nat.below
#param nat.brec_on

#param nat.add._main
#param_rec_ax pprod.fst pprod.snd
#param_rec_ax id nat.add nat.mul list.append
#param_rec_ax bor band bnot bxor
#param_rec_ax eq.cases_on eq.drec


#print nat.param.«2»

def nat.below.param : Π (C0 : nat -> Sort.{l}) (C1 : nat -> Sort.{l'}) (CR : Pi (n0 : nat)
 (n1 : nat) (nR : nat.param.«2» n0 n1) (x0 : C0 n0) (x1 : C1 n1), Prop)
 (n0 : nat) (n1 : nat) (nR : nat.param.«2» n0 n1)
  (x0 : nat.below.{l} C0 n0) (x1 : nat.below.{l'} C1 n1), Prop :=
λ (C0 : ℕ → Sort l) (C1 : ℕ → Sort l')
(CR : Π (n0 n1 : ℕ), nat.param.«2» n0 n1 → C0 n0 → C1 n1 → Prop) (n0 n1 : ℕ) (nR : nat.param.«2» n0 n1),
  nat.rec.param.«2» (λ n0 : ℕ, Sort (max 1 l)) (λ n1 : ℕ, Sort (max 1 l'))
    (λ n0 n1 nR (α0 : Sort (max 1 l)) (α1 : Sort (max 1 l')), α0 → α1 → Prop)
      (punit.{max 1 l}) (punit.{max 1 l'}) (punit.param.«2».{(max 1 l) (max 1 l')})
    _ _
    (λ (n0 n1 : ℕ) (nR : nat.param.«2» n0 n1) (α0 : Sort (max 1 l)) (α1 : Sort (max 1 l')),
       α0 → α1 → Prop)
    punit.{(max 1 l)}
    punit.{(max 1 l')}
    punit.param.«2».{(max 1 l) (max 1 l')}
    (λ (n0 : ℕ) (ih0 : Sort (max 1 l)),
       pprod.{(max 1 l) (max 1 l)} (pprod.{l (max 1 l)} (C0 n0) ih0) punit.{(max 1 l)})
    (λ (n1 : ℕ) (ih1 : Sort (max 1 l')),
       pprod.{(max 1 l') (max 1 l')} (pprod.{l' (max 1 l')} (C1 n1) ih1)
         punit.{(max 1 l')})
    (λ (n0 n1 : ℕ) (nR : nat.param.«2» n0 n1) (ih0 : Sort (max 1 l)) (ih1 : Sort (max 1 l'))
     (ihR : ih0 → ih1 → Prop),
       pprod.param.«2».{(max 1 l) (max 1 l) (max 1 l') (max 1 l')}
         (pprod.{l (max 1 l)} (C0 n0) ih0)
         (pprod.{l' (max 1 l')} (C1 n1) ih1)
         (pprod.param.«2».{l (max 1 l) l' (max 1 l')} (C0 n0) (C1 n1) (CR n0 n1 nR) ih0 ih1 ihR)
         punit.{(max 1 l)}
         punit.{(max 1 l')}
         punit.param.«2».{(max 1 l) (max 1 l')})
    n0
    n1
    nR

#print test


#param_axiom nat.add
set_option formatter.hide_full_terms false

def empty.rec.type := Π (C : empty → Sort l) (n : empty), C n
#param empty.rec.type
#print empty.rec.type.param.«2»

#check empty.param.«2»
#check empty.param.«2».rec
#param eq
#print eq.drec
#param eq.drec
#param eq.cases_on

#print classical.choice

#param_axiom classical.choice
example : false :=
let R := nonempty.param.«2» bool bool (≠) in
classical.choice.param.«2» bool bool (≠) ⟨ff⟩ ⟨tt⟩
  (⟨_, _, _, ff, tt, bool.ff_ne_tt⟩ : R ⟨ff⟩ ⟨tt⟩) rfl


def P : (ℕ → ℕ) → Prop := λ f, f nat.zero = nat.zero

run_cmd do
  let trace_unify (e1 e2 : expr) : tactic unit := (do
    let s := simp_lemmas.mk,
    trace $ "try to unify " ++ to_string e1 ++ " with " ++ to_string e2,
    unify e1 e2 transparency.all,
    trace $ "unify successful between " ++ to_string e1 ++ " with " ++ to_string e2),
  t1 ← to_expr ``(n_id),
  t2 ← to_expr ``(λ (a0 : nat), _),
  trace_unify t1 t2

run_cmd do
  let trace_unify (e1 e2 : expr) : tactic unit := (do
    let s := simp_lemmas.mk,
    e1 ← s.dsimplify [] e1 <|> return e1, e2 ← s.dsimplify [] e2 <|> return e2,
    trace $ "try to unify " ++ to_string e1 ++ " with " ++ to_string e2,
    unify e1 e2 transparency.all,
    trace $ "unify successful between " ++ to_string e1 ++ " with " ++ to_string e2),
  t1 ← to_expr ``(λ (a0 : nat), n_id._main a0 = nat.zero),
  t2 ← to_expr ``(λ (a0 : nat), n_id a0 = nat.zero),
  trace_unify t1 t2

#exit
t1 ← to_expr ``(Π (a0 : nat) (a1 : nat) (aR : nat.param.«2» a0 a1),
    nat.param.«2» (n_id._main a0) (n_id._main a1)),
  t2 ← to_expr ``(Π (a0 : nat) (a1 : nat) (aR : nat.param.«2» a0 a1),
    nat.param.«2» (n_id a0) (n_id a1)),
  trace_unify t1 t2


example : n_id = n_id2 := rfl -- succeeds

run_cmd tactic.add_decl $ declaration.thm `nat.n_id_eq_eta_n_id []
  `(n_id = λ n, n_id n) (pure `(@rfl _ n_id))
#print nat.n_id_eq_eta_n_id

/- run_cmd (do
  l ← mk_fresh_name,
  let u := level.param l,
  let params := [(sort u : expr)],
  let ty : expr := pi "a" binder_info.default (var 0)
    $ pi "a" binder_info.default (var 1) $ sort level.zero,
  let ctorty : expr := pi "a" binder_info.default (var 0)
    $ mk_app (const `myeq [u]) [var 1, var 0, var 0],
  let inds := [((`myeq, ty),
    [{environment.intro_rule . constr := `refl, type := ctorty}])],
  updateex_env $ λe, e.add_ginductive options.mk [l] params inds ff) -/
/-
run_cmd (do
  l ← mk_fresh_name, let u := level.param l,
  let ty : expr := pi "α" binder_info.implicit (sort u)
    $ pi "a" binder_info.default (var 0)
    $ pi "a" binder_info.default (var 1) $ sort level.zero,
  let ctorty : expr := pi "α" binder_info.implicit (sort u)
    $ pi "a" binder_info.default (var 0)
    $ mk_app (const `myeq [u]) [var 1, var 0, var 0],
  let (params, ty) := split_pis (some 1) ty,
  let (_, ctorty) := split_pis (some 1) ctorty,
  let inds := [((`myeq, ty),
    [{environment.intro_rule . constr := `refl, type := ctorty}])],
  updateex_env $ λe, e.add_ginductive options.mk [l] params inds ff)
 -/




#check list
#print list.rec
#print eq.rec
#print eq.drec

def list.rec.type := Π {T : Type u} {C : list.{u} T → Sort l},
  C list.nil.{u} → (Π (hd : T) (tl : list.{u} T), C tl → C (hd :: tl)) → Π (n : list.{u} T), C n
#param list.rec.type
#print list.param.«2».rec
#print list.rec.type.param.«2»

inductive vec (α : Sort u) : ℕ → Type u
| vnil {} : vec nat.zero
| vcons {n : ℕ}  (vhd : α) (vtl : vec n) : vec n.succ
#print vec.rec
#param vec


def vec.rec.type := Π {α : Sort u} {C : Π (a : ℕ), vec.{u} α a → Sort l},
  C nat.zero vec.vnil.{u} →
  (Π {n : ℕ} (vhd : α) (vtl : vec.{u} α n), C n vtl → C (nat.succ n) (vec.vcons.{u} vhd vtl)) →
  Π {a : ℕ} (n : vec.{u} α a), C a n
#param vec.rec.type
#print vec.rec.type.param.«2»

#check vec.param.«2».rec

def id_param2 :Π (α0 α1 : Sort u) (αR : α0 → α1 → Sort u) (a0 : α0) (a1 : α1), αR a0 a1 → αR (id.{u} a0) (id.{u} a1)
   := λ (α0 α1 : Sort u) (αR : α0 → α1 → Sort u) (a0 : α0) (a1 : α1) (aR : αR a0 a1), aR


#check bool.param.«2»
#print nat.rec
#print nat.param.«2».rec
#print nat.succ
#print nat.succ.param.«2»
#print punit.param.«2»
#print list.rec
#print list.param.«2».rec

#param id_rhs
#param nat.has_zero
#param nat.pred._main

run_cmd do
  let trace_unify (e1 e2 : expr) : tactic unit := (do
    trace $ "try to unify " ++ to_string e1 ++ " with " ++ to_string e2,
    unify e1 e2 transparency.all,
    trace $ "unify successful between " ++ to_string e1 ++ " with " ++ to_string e2),
  let c1 : expr tt := const `nat.pred [],
  let c2 : expr tt := const `nat.pred._main [],
  trace_unify c1 c2, -- success
  trace "",
  let eta_nat t := lam `n bid (const `nat []) $ mk_app t [var 0],
  trace_unify (eta_nat c1) (eta_nat c2) -- failure!


#param nat.pred
#print nat.pred
#print nat.cases_on


#print declaration

#print expr

#print macro_def
#print has_zero.rec
#print has_zero.param.«2»

def has_zero.rec.type :=
 Π {α : Type u} {C : has_zero.{u} α → Sort l},
  (Π (zero : α), C {zero := zero}) → Π (n : has_zero.{u} α), C n
#print has_zero.rec.type
def has_zero_rec_test : has_zero.rec.type := @has_zero.rec.{u l}

run_cmd (do
  let n := `has_zero.zero,
  env ← get_env,
  decl ← env.get n,
  match decl with
  | (declaration.defn x univs α body hints b) := do
    trace ("defn", x, univs, α, body, b),
    trace $ env.unfold_all_macros body
  | (declaration.thm x univs α tasks) := trace ("thm", x, univs, α)
  | (declaration.cnst x univs α b) := trace ("cnst", x, univs, α, b)
  | (declaration.ax x univs α) := trace ("ax", x, univs, α)
  end)


#param has_zero.rec.type
#print has_zero.rec.type.param.«2»


#print has_zero.zero

#print has_zero.zero.param.«2»

#print nat.below

--------------------------
-- Not working examples --
--------------------------

#param nat.below

def nat.rec.type := Π {C : ℕ → Sort l}, C 0 → (Π (n : ℕ), C n → C (nat.succ n)) → Π (n : ℕ), C n

#print nat.rec.type
#param nat.rec.type

def nat.rec.type.param.«2» : nat.rec.type → nat.rec.type → Sort (imax (max 1 (l+1)) l 1 l) :=
  λ (f0 f1 : Π (C0 : ℕ → Sort l), C0 0 → (Π (n0 : ℕ), C0 n0 → C0 (nat.succ n0)) → Π (n0 : ℕ), C0 n0),
  Π (C0 C1 : ℕ → Sort l) (CR : Π (a0 a1 : ℕ), nat.param.«2» a0 a1 → C0 a0 → C1 a1 → Sort l) (a0 : C0 0)
  (a1 : C1 0),
    CR 0 0 (has_zero.zero.param.«2» ℕ ℕ nat.param.«2» nat.has_zero nat.has_zero nat.has_zero.param.«2») a0
      a1 →
    Π (a0_1 : Π (n0 : ℕ), C0 n0 → C0 (nat.succ n0)) (a1_1 : Π (n1 : ℕ), C1 n1 → C1 (nat.succ n1)),
      (Π (n0 n1 : ℕ) (nR : nat.param.«2» n0 n1) (a0 : C0 n0) (a1 : C1 n1),
         CR n0 n1 nR a0 a1 →
         CR (nat.succ n0) (nat.succ n1) (nat.succ.param.«2» n0 n1 nR) (a0_1 n0 a0) (a1_1 n1 a1)) →
      Π (n0 n1 : ℕ) (nR : nat.param.«2» n0 n1), CR n0 n1 nR (f0 C0 a0 a0_1 n0) (f1 C1 a1 a1_1 n1)





def nat.below.param.«2» : Π (C0 C1 : ℕ → Sort l),
  (Π (n0 n1 : ℕ), nat.param.«2» n0 n1 → C0 n0 → C1 n1 → Sort l) →
  Π (n0 n1 : ℕ), nat.param.«2» n0 n1 → nat.below C0 n0 → nat.below C1 n1 → Sort (max 1 l) :=
λ (C0 C1 : ℕ → Sort l) (CR : Π (n0 n1 : ℕ), nat.param.«2» n0 n1 → C0 n0 → C1 n1 → Sort l)
(n0 n1 : ℕ) (nR : nat.param.«2» n0 n1),

nat.rec.param.«2»  (λ (n0 : ℕ), Sort (max 1 l)) (λ (n1 : ℕ), Sort (max 1 l))
    (λ (n0 n1 : ℕ) (nR : nat.param.«2» n0 n1)
    (α0 α1 : Sort (max 1 l)), α0 → α1 → Sort (max 1 l))
    punit.param.«2»
    (λ (n0 : ℕ) (ih0 : Sort (max 1 l)), pprod (pprod (C0 n0) ih0) punit)
    (λ (n1 : ℕ) (ih1 : Sort (max 1 l)), pprod (pprod (C1 n1) ih1) punit)
    (λ (n0 n1 : ℕ) (nR : nat.param.«2» n0 n1) (ih0 ih1 : Sort (max 1 l)) (ihR : ih0 → ih1 → Sort (max 1 l)),
       pprod.param.«2» (pprod (C0 n0) ih0) (pprod (C1 n1) ih1)
         (pprod.param.«2» (C0 n0) (C1 n1) (CR n0 n1 nR) ih0 ih1 ihR)
         punit
         punit
         punit.param.«2»)
    n0
    n1
    nR

run_cmd do
  let e := `(λ α : Type, λ x : α, x),
  let t := `(∀ α : Type, α → α),
  (t0,t1,tR) ← t.param 2,
  (e0,e1,eR) ← e.param 2,
  teR ← infer_type eR,
  unify teR (tR.mk_app [e, e])

#exit
