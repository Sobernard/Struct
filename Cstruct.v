(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 INRIA.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

Require Import Reals Rtrigo1.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq choice.
From mathcomp Require Import fintype algC ssrint ssrnum complex ssralg finfun.
From mathcomp Require Import ssrnat div intdiv mxpoly rat bigop polydiv.
From mathcomp Require Import fieldext poly finset separable polyorder.
From structs Require Import archi Rstruct.

Import GRing.Theory Num.Def Num.Theory Archi.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.

(* Definition des complexes sur les réels de Coq *)

Definition complexR := R[i].

Canonical complexR_eqType := [eqType of complexR].
Canonical complexR_choiceType := [choiceType of complexR].
Canonical complexR_countype := [choiceType of complexR].
Canonical complexR_zmodType := [zmodType of complexR].
Canonical complexR_lmodType := Eval hnf in [lmodType R of complexR].
Canonical complexR_ringType := Eval hnf in [ringType of complexR].
Canonical complexR_comRingType := Eval hnf in [comRingType of complexR].

(* These two should disappear once the canonical algebra structure is in the
  complex.v file, and be replaced by a simple canonical ... *)
Program Canonical complexR_lalgType := LalgType R complexR _.
Next Obligation. 
by move=> a [b c] [d e] /=; rewrite -!mulrA -mulrDr -mulrBr.
Qed.

Program Canonical complexR_algType := AlgType R complexR _.
Next Obligation.
by move=> a [b c] [d e] /=; simpc; rewrite ![_ * (a * _)]mulrCA -mulrDr -mulrBr.
Qed.

Canonical complexR_unitRingType := Eval hnf in [unitRingType of complexR].
Canonical complexR_comUnitRingType := Eval hnf in [comUnitRingType of complexR].
Canonical complexR_unitAlgType := Eval hnf in [unitAlgType R of complexR].
Canonical complexR_idomainType := Eval hnf in [idomainType of complexR].
Canonical complexR_fieldType := Eval hnf in [fieldType of complexR].
Canonical complexR_decDieldType := Eval hnf in [decFieldType of complexR].
Canonical complexR_closedFieldType := Eval hnf in [closedFieldType of complexR].
Canonical complexR_numDomainType := Eval hnf in [numDomainType of complexR].
Canonical complexR_numFieldType := Eval hnf in [numFieldType of complexR].
Canonical complexR_numClosedFieldType := Eval hnf in [numClosedFieldType of complexR].
Canonical complexR_archiNumDomainType := Eval hnf in [archiNumDomainType of complexR].
Canonical complexR_archiNumFieldType := Eval hnf in [archiNumFieldType of complexR].
Canonical complexR_archiNumClosedFieldType := Eval hnf in [archiNumClosedFieldType of complexR].

(* Récupération des notations *)

Notation Creal := (@Num.Def.Rreal complexR_numDomainType).
Notation Cint := (@Cint complexR_archiNumDomainType).
Notation Cnat := (@Cnat complexR_archiNumDomainType).

(* Injections *)

Notation QtoC := (ratr : rat -> complexR).
Notation ZtoQ := (intr : int -> rat).

Notation ZtoC := (intr : int -> complexR).

Definition ZtoCE :=
  let CnF := complexR_numFieldType in
  let ZtoCm := intmul1_rmorphism CnF in
  ((rmorph0 ZtoCm, rmorph1 ZtoCm, rmorphMn ZtoCm, rmorphN ZtoCm, rmorphD ZtoCm),
   (rmorphM ZtoCm, rmorphX ZtoCm),
   (rmorphMz ZtoCm, @intr_norm CnF, @intr_sg CnF, @intr_eq0 CnF),
   =^~ (@ler_int CnF, @ltr_int CnF, (inj_eq (@intr_inj CnF)))).

(* retour à R depuis les complexes *)
Notation Re_R := (@complex.Re R_rcfType).
Notation Im_R := (@complex.Im R_rcfType).
Notation norm_R := ComplexField.normc.

(* here again, the canonical refering to ComplexField should disappear *)
Canonical Re_R_additive := [additive of Re_R].
Canonical ComplexField.Re_linear.
Canonical Re_R_linear := [linear of Re_R].
Canonical Im_R_additive := [additive of Im_R].
Canonical ComplexField.Im_linear.
Canonical Im_R_linear := [linear of Im_R].

Notation RtoC := (real_complex R : R -> complexR).

Ltac RtoC_simpl := 
  rewrite -?complexRe -?complexIm -?[`| _ |]/(((norm_R _)%:C)%C) -?[((_)%:C)%C]/(RtoC _) /=.

Lemma RtoC_inj : injective RtoC.
Proof. by move => x y /eqP; rewrite /RtoC eq_complex /= eq_refl andbT => /eqP. Qed.

Lemma RtoC_norm x : RtoC `|x| = `|RtoC x|.
Proof.
rewrite normc_def; RtoC_simpl; apply/eqP; rewrite (inj_eq RtoC_inj); apply/eqP.
by rewrite expr0n /= addr0 sqrtr_sqr.
Qed.

Lemma ler_RtoC x y : (RtoC x <= RtoC y) = (x <= y).
Proof. by rewrite -lecR; RtoC_simpl. Qed.

Lemma ltr_RtoC x y : (RtoC x < RtoC y) = (x < y).
Proof. by rewrite -ltcR; RtoC_simpl. Qed.

Definition RtoCE :=
  let CnF := R_rcfType in
  let RtoCm := ComplexField.real_complex_rmorphism CnF in
  ((rmorph0 RtoCm, rmorph1 RtoCm, rmorphMn RtoCm, rmorphN RtoCm, rmorphD RtoCm),
   (rmorphM RtoCm, rmorphX RtoCm),
   (rmorphMz RtoCm, RtoC_norm),
   =^~ (ler_RtoC, ltr_RtoC, (inj_eq RtoC_inj))).

(* tactiques *)
Definition C_simpl :=
  (addr0, add0r, subr0, mulr0, mul0r, mulr1, mul1r, mulr0n, mulrS, expr0, exprS).

(* complex exponential *)

Definition Cexp (z : complexR) : complexR :=
  RtoC (exp(Re_R z)) * (RtoC (cos (Im_R z)) + 'i * RtoC (sin (Im_R z))).

Lemma Cexp_exp x :
  x \in Creal -> Cexp(x) = RtoC (exp(Re_R x)).
Proof.
move=> /Creal_ImP; RtoC_simpl; rewrite /Cexp => /eqP.
rewrite /eqP fmorph_eq0 => /eqP ->; rewrite sin_0 cos_0 /=.
by rewrite !RtoCE !C_simpl.
Qed.

Lemma Cexp0 :
  Cexp(0) = 1.
Proof. by rewrite /Cexp /= sin_0 cos_0 !RtoCE !C_simpl expR0. Qed.

Lemma CexpRD x y :
  Cexp(x) * Cexp(y) = Cexp(GRing.add x y).
Proof.
rewrite /Cexp mulrA [X in X *_ = _]mulrC mulrA -rmorphM /= expRD addrC -mulrA.
rewrite -raddfD /= mulC_rect -!rmorphM -rmorphD -rmorphB /= -cos_add.
by rewrite [X in RtoC( X + _)]mulrC -sin_add -!raddfD [y + x]addrC /=.
Qed.

Lemma Cexp_morph : {morph Cexp : x y / x + y >-> x * y}.
Proof. by move=> x y; rewrite CexpRD. Qed.


Lemma CexpRX x :
  forall n : nat,
    Cexp(x) ^+ n = Cexp(x *+ n).
Proof.
elim => [|n Ihn]; rewrite !C_simpl; first by rewrite Cexp0.
by rewrite Ihn Cexp_morph.
Qed.

Lemma CscaleE (x : R) (y : complexR) :
  x *: y = RtoC x * y.
Proof. by case: y => [yr yi]; rewrite /GRing.scale /= /RtoC; simpc. Qed.


Section MinPoly.

Local Notation "x 'is_algebraic'" := (algebraicOver QtoC x)
  (at level 55).

Lemma separable_polyZ (R : idomainType) (p : {poly R}) (a : R) : 
    a != 0 -> separable_poly (a *: p) = separable_poly p.
Proof.
by move=> an0; rewrite /separable_poly derivZ coprimep_scalel ?coprimep_scaler.
Qed.

Definition psep (R : idomainType) (p : {poly R}) :=
  let p_ := gcdp p (deriv p) in
    (lead_coef p_) *: (p %/ p_).

Lemma psep_separable (R : idomainType) (p : {poly R}) :
  p != 0 -> separable_poly (psep p).
Proof. 
move=> p_neq0; rewrite /psep separable_polyZ ?make_separable //.
by rewrite lead_coef_eq0 gcdp_eq0 negb_and p_neq0.
Qed.

Lemma psep_neq0 (R : idomainType) (p : {poly R}) :
  p != 0 -> psep p != 0.
Proof.
move=> p_neq0; pose p_ := gcdp p (deriv p).
have lc_neq0 : lead_coef p_ != 0.
  by rewrite lead_coef_eq0 gcdp_eq0 negb_and p_neq0.
by rewrite /psep scale_poly_eq0 negb_or lc_neq0 andTb dvdp_div_eq0 ?dvdp_gcdl.
Qed.

(* :TODO: remove once the changes are made in polyorder *)
Lemma size_deriv (R : numDomainType) (p : {poly R}) : size p^`() = (size p).-1.
Proof.
have [lep1|lt1p] := leqP (size p) 1.
  by rewrite {1}[p]size1_polyC // derivC size_poly0 -subn1 (eqnP lep1).
rewrite size_poly_eq // mulrn_eq0 -subn2 -subSn // subn2.
by rewrite lead_coef_eq0 -size_poly_eq0 -(subnKC lt1p).
Qed.

(* :TODO: remove once the changes are made in polyorder *)
Lemma mu_deriv (R : numDomainType) : forall x (p : {poly R}), root p x ->
  \mu_x (p^`()) = (\mu_x p - 1)%N.
Proof.
move=> x p px0; have [-> | nz_p] := eqVneq p 0; first by rewrite derivC mu0.
have [q nz_qx Dp] := mu_spec x nz_p.
case Dm: (\mu_x p) => [|m]; first by rewrite Dp Dm mulr1 (negPf nz_qx) in px0.
rewrite subn1 Dp Dm !derivCE exprS mul1r mulrnAr -mulrnAl mulrA -mulrDl.
rewrite cofactor_XsubC_mu // rootE !(hornerE, hornerMn) subrr mulr0 add0r.
by rewrite mulrn_eq0.
Qed.

(* :TODO: remove once the changes are made in polyorder *)
Lemma mu_deriv_root (R : numDomainType) : 
  forall x (p : {poly R}), p != 0 -> root p x ->
  \mu_x p  = (\mu_x (p^`()) + 1)%N.
Proof.
by move=> x p p0 rpx; rewrite mu_deriv // subn1 addn1 prednK // mu_gt0.
Qed.

Lemma psep_root (F E : numFieldType) (f : {rmorphism F -> E}) (p : {poly F}) (x : E) :
  p != 0 -> root (map_poly f p) x -> root (map_poly f (psep p)) x.
Proof.
move=> p_neq0 root_p; pose p_ := gcdp p (deriv p).
have lc_neq0 : lead_coef p_ != 0.
  by rewrite lead_coef_eq0 gcdp_eq0 negb_and p_neq0.
rewrite map_polyZ /=; apply/rootP/eqP. 
rewrite hornerZ mulf_eq0; apply/orP; right; apply/eqP/rootP.
move: (divpK (dvdp_gcdl p (deriv p))); rewrite -/p_ => eq_p.
rewrite -mu_gt0; last first.
  rewrite map_poly_eq0; apply/negP => /eqP H; rewrite H mul0r in eq_p.
  by rewrite -eq_p eq_refl in p_neq0.
have fp_neq0 : (map_poly f (p %/ p_)) * (map_poly f p_) != 0.  
  by rewrite -rmorphM eq_p map_poly_eq0.
rewrite -(ltn_add2r (\mu_x (map_poly f p_))) add0n -mu_mul //.
rewrite -rmorphM /= divpK ?dvdp_gcdl //.
rewrite (mu_deriv_root _ root_p) ?map_poly_eq0 // addn1 ltnS /p_ /=. 
rewrite gcdp_map deriv_map /=.
have H := (divpK (dvdp_gcdr (map_poly f p) (map_poly f p^`()))).
rewrite -{2}H mu_mul ?leq_addl // H -size_poly_eq0 -deriv_map size_deriv.
rewrite -lt0n -ltnS prednK; last by rewrite lt0n size_poly_eq0 map_poly_eq0.
by apply: (root_size_gt1 _ root_p); rewrite map_poly_eq0.
Qed.



Section MinPoly_byalgC.

Lemma poly_caract_byalgC x : x is_algebraic ->
  {p | [/\ (p \is monic), separable_poly p, irreducible_poly p &    
    forall q, root (map_poly QtoC q) x = (p %| q)]}.
Proof.
move=> /integral_algebraic /sig2W[p pmonic proot].
move H : (size p) => n.
case: n H.
  by move/eqP; move/monic_neq0: pmonic; rewrite -size_poly_eq0 => /negbTE ->.
case => [size_p | n eq_n].
  move/(root_size_gt1 _): proot; rewrite map_poly_eq0 => H.
  by move/monic_neq0: pmonic; move/H; rewrite size_map_poly size_p.
elim: n {-2}n (leqnn n) p pmonic proot eq_n => [n /= |].
  rewrite leqn0 => /eqP -> p pmonic proot_x size_p.
  exists p; split => // [||q].
  + move/eqP: (size_deriv p); rewrite size_p /= => /size_poly1P[a a_neq0 eq_p'].
    by rewrite /separable_poly eq_p' -alg_polyC coprimep_scaler ?coprimep1.
  + rewrite /irreducible_poly size_p.
    split => // q size_q div_q; rewrite -dvdp_size_eqp // eqn_leq.
    apply/andP; split; first by apply/dvdp_leq; first apply/monic_neq0.
    rewrite size_p ltn_neqAle eq_sym size_q /= lt0n size_poly_eq0.
    by apply/(dvdpN0 div_q (monic_neq0 pmonic)).    
  + move: proot_x; rewrite !root_factor_theorem => /dvdp_size_eqp.
    rewrite size_XsubC size_map_poly size_p eq_refl => /esym H.
    rewrite -(dvdp_map (ratr_rmorphism complexR_numFieldType)) /=.    
    by apply/eqp_dvdl.
move=> n ihn np lenp p pmonic proot_x size_p.
have [s_root eq_s] := (closed_field_poly_normal 
                                    (map_poly (ratr_rmorphism algCnumField) p)).
pose xC := nth 0 s_root 0.
have proot_xC : root (map_poly ratr p) xC.
  apply/rootP/eqP; rewrite eq_s hornerZ mulf_eq0 lead_coef_eq0 map_poly_eq0.
  rewrite (negbTE (monic_neq0 _)) //= horner_prod prodf_seq_eq0.
  apply/hasP; exists xC; last by rewrite andTb hornerXsubC subrr.
  rewrite /xC mem_nth //.
  have -> : size s_root = (size p).-1.
    rewrite -(size_map_poly (ratr_rmorphism algCnumField)) /= eq_s size_scale.
      by rewrite size_prod_XsubC.
    by rewrite lead_coef_eq0 map_poly_eq0 monic_neq0 ?pmonic.
  by rewrite size_p /=.
have isQ := algebraics_fundamentals.rat_algebraic_decidable 
                                 Algebraics.Implementation.algebraic.
have [q [qmonic root_qxC irr_q]] := 
     algebraics_fundamentals.minPoly_decidable_closure isQ 
                                    (Algebraics.Implementation.algebraic xC).
have size_q : (1 < size q)%N.
  rewrite -(size_map_poly (ratr_rmorphism algCnumField)). 
  by rewrite (@root_size_gt1 _ xC) ?map_poly_eq0 ?monic_neq0.
case: (boolP (root (map_poly ratr q) x)) => [qroot_x | q_notroot].
  exists q; do? split => //.
    suff -> : q = psep q by rewrite psep_separable ?monic_neq0.
    move/(irredp_XsubCP irr_q): (dvdp_gcdl q q^`()) => [].
      rewrite /psep; move/eqp_eq; rewrite lead_coef1 scale1r => ->.
      set z := lead_coef (gcdp _ _); rewrite alg_polyC lead_coefC -mul_polyC.
      rewrite divpKC //; apply/modp_eq0P; rewrite modpC // /z lead_coef_eq0.
      rewrite gcdp_eq0 negb_and -size_poly_eq0 -lt0n.
      by apply/orP; left; rewrite (ltn_trans _ size_q).  
    move/eqp_size/esym/eq_leq; have := (@leq_gcdpr _ q q^`()) .
    rewrite -size_poly_eq0 size_deriv -lt0n -(ltn_add2r 1) ?addn1 prednK //.
      move/(_ size_q) => legcdp_1 le_q_gcdp.
      move: (leq_trans le_q_gcdp legcdp_1).
      by rewrite -ltnS prednK ?ltnn // (ltn_trans _ size_q).
    by rewrite (ltn_trans _ size_q).
  move=> q0; apply/idP/idP=> [q0root_x | /dvdpP[r ->]]; last first.
    by rewrite rmorphM rootM qroot_x orbT.
  suffices /eqp_dvdl <-: gcdp q q0 %= q by apply: dvdp_gcdr.
  rewrite irr_q ?dvdp_gcdl ?gtn_eqF // -(size_map_poly (ratr_rmorphism complexR_numFieldType)). 
  rewrite gcdp_map /= (@root_size_gt1 _ x) ?root_gcd ?q0root_x ?qroot_x //.
  by rewrite gcdp_eq0 negb_and map_poly_eq0 monic_neq0.
have: (q %| p).
  suffices /eqp_dvdl <-: gcdp q p %= q by apply: dvdp_gcdr.
  rewrite irr_q ?dvdp_gcdl ?gtn_eqF //. 
  rewrite -(size_map_poly (ratr_rmorphism algCnumField)) gcdp_map /=.
  rewrite (@root_size_gt1 _ xC) ?root_gcd ?px0 //.
    by rewrite gcdp_eq0 negb_and map_poly_eq0 monic_neq0.
  by rewrite proot_xC root_qxC.
rewrite dvdp_eq; set r := _ %/ _ => /eqP eq_p.
have rmonic : r \is monic.
  by move/(monicMr r): qmonic; rewrite -eq_p pmonic.
have root_r : root (map_poly ratr r) x.  
  by move: proot_x; rewrite eq_p rmorphM /= rootM (negbTE q_notroot) orbF.
have size_r : (1 < size r)%N.
  rewrite -(size_map_poly (ratr_rmorphism complexR_numFieldType)). 
  by rewrite (@root_size_gt1 _ x) ?map_poly_eq0 ?monic_neq0.
have Hsize : ((size r).-2 <= n)%N.
  rewrite -(leq_add2r 1) !addn1.
  apply: (leq_trans _ lenp); rewrite -(leq_add2r 2) !addn2.
  rewrite -size_p prednK ?prednK //; first last.
  + by rewrite -(ltn_add2r 1) ?addn1 prednK // (ltn_trans _ size_r).
  + by rewrite (ltn_trans _ size_r).
  + rewrite eq_p size_monicM ?monic_neq0 //. 
    rewrite -subn1 -addnBA ?subn1 ?(ltn_trans _ size_q) //.
    rewrite -[X in (X < _)%N]addn0 ltn_add2l.
    by rewrite -(ltn_add2r 1) ?addn1 prednK // (ltn_trans _ size_q).
apply: (ihn (size r).-2 Hsize r rmonic root_r).
rewrite prednK ?prednK //.
  by rewrite (ltn_trans _ size_r).
by rewrite -(ltn_add2r 1) ?addn1 prednK // (ltn_trans _ size_r).
Qed.

End MinPoly_byalgC.

Lemma ratr_eq0 (x : rat) : ((QtoC x) == (0: complexR)) = (x == 0).
Proof.
by rewrite -numq_eq0 mulf_eq0 invr_eq0 !intr_eq0 (negbTE (denq_neq0 x)) orbF.
Qed.

Lemma polyZ_algebraic (x : complexR) (p : {poly int}) :
  p != 0 -> root (map_poly ZtoC p) x -> x is_algebraic.
Proof.
move=> p_neq0 rootpx; rewrite /algebraicOver.
exists (map_poly intr p).
  by rewrite map_poly_eq0_id0 // intr_eq0 lead_coef_eq0.
have ZtoQtoC : QtoC \o intr =1 ZtoC by move=> y /=; rewrite ratr_int.
by rewrite -map_poly_comp (eq_map_poly ZtoQtoC).
Qed.

Lemma poly_algebraic (x : complexR) (p : {poly complexR}) :
  p != 0 -> root p x -> p \is a polyOver Cint -> x is_algebraic.
Proof.
move=> p_neq0 rootpx /floorCpP[q eq_p_q]; rewrite /algebraicOver.
have ZtoQtoC : QtoC \o intr =1 ZtoC by move=> y /=; rewrite ratr_int.
exists (map_poly intr q).
  move: p_neq0; rewrite eq_p_q -(eq_map_poly ZtoQtoC) map_poly_comp.
  by rewrite map_poly_eq0.
by rewrite -map_poly_comp (eq_map_poly ZtoQtoC) -eq_p_q.
Qed.

Lemma poly_caract_int (x : complexR) : x is_algebraic ->
    {p : {poly int} | [/\ (zcontents p = 1),
      irreducible_poly p, separable_poly (map_poly ZtoC p)
      & forall q : {poly int}, root (map_poly ZtoC q) x = (p %| q)]}.
Proof.
move=> algebraic_x.
have [r [mon_r sep_r [irr_r div_r] root_r]] := (poly_caract_byalgC algebraic_x).
have [q [a a_neq0 r_eq]] := (rat_poly_scale r).
have q_neq0 : q != 0.
  apply/negP => /eqP q_eq0; move: r_eq; rewrite q_eq0 map_poly0 scaler0.
  by apply/eqP/monic_neq0.
have eq_qz : map_poly ZtoQ (zprimitive q) = ((zcontents q)%:~R^-1 * a%:~R) *: r. 
  rewrite r_eq -scalerA [X in _ *: X]scalerA mulfV ?intr_eq0 ?a_neq0 // scale1r.
  rewrite [X in _ *: _ _ X]zpolyEprim map_polyZ scalerA mulrC mulfV ?scale1r //.
  by rewrite intr_eq0 zcontents_eq0 q_neq0.
have ZtoQtoC : QtoC \o intr =1 ZtoC by move=> y /=; rewrite ratr_int.
exists (zprimitive q); split.
+ by rewrite zcontents_primitive q_neq0.
+ split.
    rewrite -size_rat_int_poly eq_qz size_scale //.
    by rewrite mulf_neq0 ?invr_neq0 ?intr_eq0 ?zcontents_eq0.
  move=> p; rewrite -size_rat_int_poly.
  move=> size_p; rewrite -dvdp_rat_int eq_qz dvdp_scaler; last first.
    by rewrite mulf_neq0 ?invr_neq0 ?intr_eq0 ?zcontents_eq0.
  move/(div_r _ size_p)/eqpP => [[b1 b2]] /= /andP[b1_n0 b2_n0] eq_b.
  rewrite -dvdp_size_eqp. 
    rewrite size_zprimitive -size_rat_int_poly -(size_scale _ b1_n0) eq_b.
    rewrite (size_scale _ b2_n0) r_eq size_scale ?invr_eq0 ?intr_eq0 //.
    by rewrite size_rat_int_poly.
  rewrite -dvdp_rat_int eq_qz; apply/dvdpP. 
  set u := (_ * _).
  exists (u * b2^-1 * b1)%:P.
  rewrite mul_polyC -[in RHS]scalerA -[in RHS]scalerA eq_b.
  by congr (u *: _); rewrite scalerA mulrC mulfV ?scale1r.
+ rewrite -(eq_map_poly ZtoQtoC) map_poly_comp eq_qz /= map_polyZ /=.
  rewrite separable_polyZ ?separable_map //.
  by rewrite ratr_eq0 mulf_neq0 ?invr_eq0 ?intr_eq0 ?zcontents_eq0.
+ move=> p; rewrite -(eq_map_poly ZtoQtoC) map_poly_comp root_r r_eq.
  rewrite dvdp_scalel ?invr_eq0 ?intr_eq0 //.
  by rewrite dvdp_rat_int [q in LHS]zpolyEprim dvdp_scalel ?zcontents_eq0.
Qed.

Definition polyMinZ (x : complexR) (H : x is_algebraic) :=
  sval (poly_caract_int H).

Definition polyMin (x : complexR) (H : x is_algebraic) :=
  map_poly ZtoC (polyMinZ H).


Lemma polyMinZ_zcontents (x : complexR) (H : x is_algebraic) : 
    zcontents (polyMinZ H) = 1.
Proof. by move: (svalP (poly_caract_int H)) => [->]. Qed.

Lemma polyMinZ_neq0 (x : complexR) (H : x is_algebraic) : (polyMinZ H) != 0.
Proof. by rewrite -zcontents_eq0 polyMinZ_zcontents. Qed.

Lemma polyMin_neq0 (x : complexR) (H : x is_algebraic) : (polyMin H) != 0.
Proof.
by rewrite map_poly_eq0_id0 ?intr_eq0 ?lead_coef_eq0 polyMinZ_neq0.
Qed.

Lemma polyMinZ_irr (x : complexR) (H : x is_algebraic) :
  irreducible_poly (polyMinZ H).
Proof. by move: (svalP (poly_caract_int H)) => []. Qed.

Lemma polyMinZ_root (x : complexR) (H : x is_algebraic) : 
  root (map_poly ZtoC (polyMinZ H)) x.
Proof.
move: (svalP (poly_caract_int H)) => [_ _ _ ->].
by rewrite dvdpp.
Qed.

Lemma polyMin_root (x : complexR) (H : x is_algebraic) : 
  root (polyMin H) x.
Proof. by rewrite polyMinZ_root. Qed.

Lemma polyMinZ_dvdp (x : complexR) (H : x is_algebraic) (q : {poly int}) :
    root (map_poly ZtoC q) x = ((polyMinZ H) %| q).
Proof. by move: (svalP (poly_caract_int H)) => []. Qed.


Lemma polyMin_dvdp (x : complexR) (H : x is_algebraic) (q : {poly complexR}):
  q \is a polyOver Cint -> root q x = ((polyMin H) %| q).
Proof.
move/floorCpP => [r ->]; rewrite polyMinZ_dvdp -dvdp_rat_int /polyMin.
rewrite -(dvdp_map (ratr_rmorphism complexR_numFieldType)) -!map_poly_comp /=.
by congr ( _ %| _); apply: eq_map_poly => y /=; rewrite ratr_int.
Qed.


Lemma polyMinZ_lcoef_gt0 (x : complexR) (H : x is_algebraic) : 
  0 < lead_coef (polyMinZ H).
Proof.
rewrite -sgz_gt0 -sgz_contents.
move: (svalP (poly_caract_int H)) => [-> _ _ _].
by rewrite sgz1.
Qed.

Lemma polyMin_lcoef_gt0 (x : complexR) (H : x is_algebraic) : 
  0 < lead_coef (polyMin H).
Proof.
by rewrite lead_coef_map_eq ?intr_eq0 ?ltr0z ?lt0r_neq0 // polyMinZ_lcoef_gt0.
Qed.


Lemma polyMinZ_separable (x : complexR) (H : x is_algebraic) :
  separable_poly (map_poly ZtoC (polyMinZ H)).
Proof. by move: (svalP (poly_caract_int H)) => []. Qed.

Lemma polyMin_separable (x : complexR) (H : x is_algebraic) :
  separable_poly (polyMin H).
Proof. by rewrite polyMinZ_separable. Qed.

Lemma polyMin_over (x : complexR) (H : x is_algebraic) :
  polyMin H \is a polyOver Cint.
Proof.
by rewrite /polyMin; apply/polyOverP => i; rewrite coef_map Cint_int.
Qed.

Lemma polyMinseq (n : nat) (f : {ffun 'I_n -> complexR}) :
  (forall i : 'I_n, f i is_algebraic) ->
  {p : {poly complexR} | [&& [forall i, root p (f i)],
  separable_poly p, p != 0, p \is a polyOver Cint & (0 < lead_coef p)]}.
Proof.
move=> f_alg; pose p i := polyMinZ (f_alg i); pose Pp := \prod_(i < n) p i.
have Pp_neq0 : Pp != 0 by apply/prodf_neq0 => i _; rewrite /p polyMinZ_neq0.
pose P := psep (map_poly ZtoQ Pp).
have ZtoQtoC : QtoC \o intr =1 ZtoC by move=> y /=; rewrite ratr_int.
have rootP i : root (map_poly QtoC P) (f i).
  apply: psep_root; rewrite ?map_poly_eq0_id0 ?intr_eq0 ?lead_coef_eq0 //.
  rewrite -map_poly_comp (eq_map_poly ZtoQtoC) rmorph_prod /=.
  apply/rootPt; rewrite horner_prod; apply/prodf_eq0; exists i => //.
  by apply/rootPt /polyMinZ_root.
have Psep : separable_poly (map_poly QtoC P).
  rewrite separable_map psep_separable ?map_poly_eq0_id0 //.
  by rewrite intr_eq0 lead_coef_eq0.
have P_neq0 : P != 0.
  by rewrite psep_neq0 // map_poly_eq0_id0 ?intr_eq0 ?lead_coef_eq0.
have : {q : {poly int} & {a : int_ZmodType | (0 < lead_coef q) 
       & P = a%:~R^-1 *: map_poly ZtoQ q}}.
  have [p_ [a /negbTE a_neq0 eq_p_p_]] := rat_poly_scale P.
  have lc_p_ : lead_coef p_ != 0.
    rewrite lead_coef_eq0; apply/negP => /eqP p__eq0.
    rewrite p__eq0 map_poly0 scaler0 in eq_p_p_.
    by rewrite eq_p_p_ eq_refl in P_neq0.
  exists ((sgr (lead_coef p_)) *: p_); exists ((sgr (lead_coef p_)) * a).
    by rewrite lead_coefZ -normrEsg normr_gt0.
  rewrite eq_p_p_ map_polyZ rmorphM invfM /=; set x := (sgr _)%:~R.
  by rewrite scalerA mulrC mulrA mulfV ?mul1r ?intr_eq0 ?sgr_eq0.
move=> [p_ [a a_gt0 eq_P_p_]].
have a_neq0 : QtoC a%:~R != 0.
  rewrite ratr_eq0; apply/negP => /eqP a_eq0. 
  by rewrite a_eq0 invr0 scale0r in eq_P_p_; rewrite eq_P_p_ eq_refl in P_neq0.
have eq_p__P : map_poly ZtoC p_ = map_poly QtoC (a%:~R *: P).
  rewrite eq_P_p_ scalerA mulfV -?ratr_eq0 // scale1r -map_poly_comp.
  by apply: eq_map_poly.
exists ((ratr a%:~R) *: (map_poly QtoC P)); apply/and5P; split.
+ by apply/forallP => i; rewrite rootZ.
+ by rewrite separable_polyZ.
+ by rewrite scale_poly_eq0 negb_or a_neq0 andTb map_poly_eq0.
+ rewrite -map_polyZ -eq_p__P; 
  by apply/polyOverP => i; rewrite coef_map Cint_int.
+ rewrite -map_polyZ -eq_p__P lead_coef_map_eq ?ltr0z //.
  rewrite intr_eq0 lead_coef_eq0; apply/negP => /eqP eq_p_.
by rewrite eq_p_ map_poly0 scaler0 in eq_P_p_; rewrite eq_P_p_ eq_refl in P_neq0.
Qed.








End MinPoly.




