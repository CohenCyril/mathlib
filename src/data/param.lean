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

import tactic
open expr native tactic
open lean.parser interactive
set_option pp.universes true

meta def expr.instantiate_lam (nv : expr) : expr → expr
| (lam nm bi tp bd) := bd.instantiate_var nv
| e := app e nv

meta def expr.mk_subst_or_app : expr → list expr → expr
| e []      := e
| e (x::xs) := (x.instantiate_lam e).mk_subst_or_app xs

private def bid := binder_info.default

meta def expr.strip_lam : expr → nat → option expr
| (lam _ _ _ bd) (nat.succ n) := bd.strip_lam n
| t 0 := return t
| _ _ := none

meta def concl : expr → expr | (pi _ _ _ ty) := concl ty | ty := ty
meta def hdapp : expr → expr | (expr.app x _) := hdapp x | x := x

meta def split_pis : option ℕ → expr → list expr × expr
| (some 0) ty := ([], ty)
| n (pi _ _ α ty) := 
  let (αs, ty) := split_pis ((λ x : ℕ, x - 1) <$> n) ty in
  (α :: αs, ty)
| _ ty := ([], ty)

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

meta def expr.param' (p : nat) (umap : name_map name): expr →
  name_map (expr × expr × expr) →
  tactic (expr × expr × expr)
| (var         db) _ := fail $ "expr.param: cannot translate a var"
| (sort        lvl) _ := do
  let lvl1 := lvl.instantiate (umap.map level.param).to_list,
  return (sort lvl, sort lvl1,
    lam "α0" bid (sort lvl) $ lam "α1" bid (sort lvl1) $
    pi "x0" bid (var 1) $ pi "x1" bid (var 1) $ sort level.zero)
| c@(const       x lvls) _ := do
    let xR := x.param p,
    /- do env ← get_env, env.get xR, /- fix: test only non current definitions -/ -/
    let lvls1 := lvls.map (λ lvl, lvl.instantiate (umap.map level.param).to_list),
    return (c, const x lvls1, const xR (lvls ++ lvls1))
| c@(local_const x pry binfo α) lconsts := lconsts.find x
| (app u v) lconsts := do
  (u0, u1, uR) ← u.param' lconsts,
  (v0, v1, vR) ← v.param' lconsts, /- trace $ "u= " ++ to_string u ++ ";   uR= " ++ to_string uR, -/
  return (app u0 v0, app u1 v1, mk_app uR [v0, v1, vR])
| (lam x binfo α body) lconsts := do
  (α0, α1, αR) ← α.param' lconsts,
  ((x0, x1, xR), lconsts, body) ← param.intro lconsts x α0 α1 αR body,
  (body0, body1, bodyR) ← body.param' lconsts,
  let t0 := body0.mk_binding lam x0,
  let t1 := body1.mk_binding lam x1,
  let tR := ((bodyR.mk_binding lam xR).mk_binding lam x1).mk_binding lam x0,
  return (t0, t1, tR)
| (pi x binfo α body) lconsts := do
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
| (elet  x α val body) lconsts :=  do
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
| exp lconsts := match exp.is_sorry with
  | some α := do
    (α0, α1, αR) ← α.param' lconsts,
    return (mk_sorry α0, mk_sorry α1, (mk_sorry αR).mk_subst_or_app [mk_sorry α0, mk_sorry α1])
  | none := fail $
    "expr.param': expression " ++ exp.to_string ++ " is not translatable"
  end

meta def expr.param (t : expr) (p := 2) (umap : name_map name) (lconst : name_map _) :=
  expr.param' p umap t lconst

meta def param.fresh_from_pis (p := 2) (umap  : _):
      name_map (expr × expr × expr) → option ℕ → expr →
    tactic ((list expr × list expr × list expr) × name_map (expr × expr × expr) × expr)
  | lconsts (some nat.zero) ty := return (([], [], []), lconsts, ty)
  | lconsts n (pi x binfo α body) := do
      let n := (λ x : ℕ, x - 1) <$> n,
      (α0, α1, αR) ← α.param p umap lconsts,
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

-- #reduce nat.pred 10000

-- #run_cmd do
--   let n := `(nat.pred 10),
--   nfn ← tactic.whnf n,
--   trace n


meta def param.recursor (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  ind_decl ← get_decl n,
  guard $ env.is_inductive n,
  let ctors := env.constructors_of n,
  let nparams := env.inductive_num_params n,
  let nindices := env.inductive_num_indices n,
  trace ("ctors:", ctors),
  let rec_name : name := n ++ "rec",
  trace ("rec_name:", rec_name),
  let Rrec_name : name := n.param p ++ "rec",
  rec_decl ← get_decl rec_name,
  let rec_ty := rec_decl.type,
  trace ("rec_ty:", rec_ty),
  let univs := rec_decl.univ_params,
  let lvls := univs.map level.param,
  trace ("lvls", lvls),
  univs1 ← univs.mmap (λ _, mk_fresh_name),
  let umap := rb_map.of_list (univs.zip univs1),
  let lvls1 := univs1.map level.param,
  let rec : expr := const rec_name lvls,
  let rec1 : expr := const rec_name lvls1,
  let Rrec : expr := const Rrec_name (lvls ++ lvls1),
  trace ("rec:", rec),
  (rec_ty0, rec_ty1, rec_tyR) ← rec_ty.param p umap mk_name_map,
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
  add_decl $ mk_definition ((n ++ "rec").param 2) (univs ++ univs1) rec_tyRrr rec_tyRrr.mk_sorry

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
  (ty0, ty1, tyR) ← ty.param p umap mk_name_map,
  trace $ ("tyR", to_string tyR),
  let tyRii := tyR.mk_subst_or_app [const n lvls, const n lvls1],
  trace $ ("tyRii", to_string tyRii),
  trace ("lvls", lvls),
  trace ("ctors:", ctors),
  ctorsR ← ctors.mmap (λ (n : name), do
    decl ← get_decl n,
    let ty := decl.type,
    (ty0, ty1, tyR) ← ty.param p umap mk_name_map,
    let tyRcc := tyR.mk_subst_or_app [const n lvls, const n lvls1],
    return (n.param p, tyRcc)),
  trace $ ("ctorsR:", to_string ctorsR),
  trace ("=========== adding inductive ============="),
  trace $ "universes " ++ (univs ++ univs1).foldr (λ u s, to_string u ++ " " ++ s) "",
  trace $ "inductive " ++ to_string n ++ " : " ++ to_string tyRii,
  ctorsR.mmap' (λ ⟨n, ty⟩, trace $ "| " ++ to_string n ++ " : " ++ to_string ty),
  add_inductive (n.param p) (univs ++ univs1) ((p + 1) * nparams) tyRii ctorsR,
  trace ("=========== inductive added ============="),
  param.recursor p n

 
meta def param.def (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  guard $ env.is_definition n,
  decl ← env.get n,
  match decl with
  | (declaration.defn _ univs α fbody _ _) := do
    univs1 ← univs.mmap (λ _, mk_fresh_name),
    let umap := rb_map.of_list (univs.zip univs1),
    let (lvls, lvls1) := (univs.map level.param, univs1.map level.param),
    trace ("def type:", α),
    trace $ ("def fbody:", to_string fbody),
    let body := env.unfold_all_macros fbody,
    trace $ ("def body:", body.to_raw_fmt),
    (_, _, αR) ← α.param 2 umap mk_name_map,
    /- trace ("def αR:", αR), -/
    (_, _, bodyR) ← body.param 2 umap mk_name_map,
    trace ("def bodyR:", bodyR.to_raw_fmt),
    let tyR := αR.mk_subst_or_app [const n lvls, const n lvls1],
    trace ("def tyR:", tyR),
    /- btyR ← infer_type bodyR, -/
    /- unify tyR btyR transparency.all,
    tyR_unif ← instantiate_mvars tyR,
    trace ("def tyR_unif:", tyR_unif), -/
    /- trace ("def tyR_unif:", tyR_unif.to_raw_fmt), -/
    trace $ "def " ++ to_string (n.param 2) ++ " : " ++ to_string tyR ++ " :=",
    trace $ bodyR,
    add_decl $ mk_definition (n.param 2) (univs ++ univs1) tyR bodyR,
    trace ("=======================")
  | _ := fail $ "param.def:  not a definition"
  end

meta def param.decl (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  if env.is_inductive n then param.inductive p n
  else if env.is_definition n then param.def p n
  else fail $ "translate: cannot translate " ++ to_string n

@[user_command]
meta def param_cmd (_ : parse $ tk "#param") : lean.parser unit := do
  ns ← many ident,
  of_tactic $ ns.mmap' (param.decl 2)

----------------------
-- Working examples --
----------------------

universes u u' v v' l l' w uu
#print empty.rec
#param empty
#print empty.param.«2»
#print empty.param.«2».rec
#param nonempty
#param punit
#param bool
#param nat
#param list
#param pprod
#param has_zero has_one has_neg has_add has_mul

#param true false and or not.
#param id

#param nat.cases_on
#print nat.below
#print nat.rec
#print nat.rec.param.«2»

#param nat.below

#check (ℕ → ℕ → Prop : Prop)

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

#param nat.brec_on

#param nat.add.below

#print nat.add._main
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


run_cmd do param.recursor 2 `empty
#check empty.param.«2»

def test :
  ∀ (C0 C1 : empty → Sort l)
    (CR : Π (a0 a1 : empty), empty.param.«2» a0 a1 → C0 a0 → C1 a1 → Prop)
    (n0 n1 : empty) (nR : empty.param.«2» n0 n1),
  CR n0 n1 nR (empty.rec C0 n0) (empty.rec C1 n1)
 := λ (C0 C1 : empty → Sort l)
      (CR : Π (n0 n1 : empty), empty.param.«2» n0 n1 → C0 n0 → C1 n1 → Prop)
    (n0 n1 : empty) (nR : empty.param.«2» n0 n1),
    @empty.param.«2».rec
      (λ (n0 n1 : empty) (nR : empty.param.«2» n0 n1), 
      CR n0 n1 nR (empty.rec.{l} C0 n0) (empty.rec.{l} C1 n1)) n0 n1 nR



#print nat.param.«2»
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

#print nat.pred._main
#print nat.cases_on

#param nat.add

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

#param has_zero.zero

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
