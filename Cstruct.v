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
From structs Require Import Rstruct.

Import GRing.Theory Num.Def Num.Theory ArchimedeanTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.

(* Definition des complexes sur les réels de Coq *)

Definition complexR := R[i].

Canonical complexR_eqType := [eqType of complexR].
Canonical complexR_choiceType := [choiceType of complexR].
Canonical complexR_zmodType := [zmodType of complexR].
Canonical complexR_ringType := [ringType of complexR].
Canonical complexR_comRingType := [comRingType of complexR].
Canonical complexR_unitRingType := [unitRingType of complexR].
Canonical complexR_comUnitRingType := [comUnitRingType of complexR].
Canonical complexR_idomainType := [idomainType of complexR].
Canonical complexR_fieldType := [fieldType of complexR].
Canonical complexR_decFieldType := [decFieldType of complexR].
Canonical complexR_closedFieldType := [closedFieldType of complexR].
Canonical complexR_numDomainType := [numDomainType of complexR].
Canonical complexR_numFieldType := [numFieldType of complexR].
Canonical complexR_numClosedFieldType := [numClosedFieldType of complexR].
Canonical complexR_numArchiDomainType := [numArchiDomainType of complexR].
Canonical complexR_numArchiFieldType := [numArchiFieldType of complexR].
Canonical complexR_numArchiClosedFieldType := [numArchiClosedFieldType of complexR].

(* Récupération des notations *)

Notation Creal := (@Num.Def.Rreal complexR_numDomainType).
Notation Cint := (@Cint complexR_numArchiDomainType).
Notation Cnat := (@Cnat complexR_numArchiDomainType).

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
Notation Re_R := complex.Re.
Notation Im_R := complex.Im.
Notation norm_R := ComplexField.normc.

Notation RtoC := (real_complex R).

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




Module ComplexTotalOrder.

Section OrderDef.

Implicit Types x y : complexR.

(* def of total order *)
Definition letc x y :=
    ('Re x < 'Re y) || (('Re x == 'Re y) && ('Im x <= 'Im y)).

Definition lttc x y :=
    (letc x y) && (x != y).

Lemma letcc : reflexive letc.
Proof. by move=> x; rewrite /letc eq_refl lerr andbT orbT. Qed.
Hint Resolve letcc.

Lemma letc_trans : transitive letc.
Proof.
move=> x y z; rewrite /letc => /orP[Ryx | /andP[/eqP <- Iyx]].
  move=> /orP[Rxz | /andP[/eqP <- _]].
  + by apply/orP; left; apply: (ltr_trans Ryx Rxz).
  + by rewrite Ryx.
move=> /orP[Ryz | /andP[/eqP <- Ixz]].
+ by rewrite Ryz.
+ by rewrite eq_refl (ler_trans Iyx Ixz) andbT orbT.
Qed.

Lemma letc_asym : antisymmetric letc.
Proof.
move=> x y /andP[]; rewrite /letc => /orP[Rxy | /andP[/eqP Rxy Ixy /=]].
  move=> /orP[ | /andP[]].
  + by rewrite ltr_gtF.
  + by rewrite (gtr_eqF Rxy).
move=> /orP[ | /andP[/eqP Ryx Iyx]].
+ by rewrite Rxy ltrr.
+ apply/eqP; rewrite eq_C -Ryx eq_refl andTb.
  by apply/eqP; apply: ler_asym; rewrite Ixy Iyx.
Qed.

Lemma lttc_neqAle x y :
  (lttc x y) = (x != y) && (letc x y).
Proof. by rewrite /lttc andbC. Qed.

Lemma letc_eqVlt x y :
  (letc x y) = (x == y) || (lttc x y).
Proof.
rewrite lttc_neqAle.
case: (boolP (x == y)) => [/eqP -> | _ //=].
by rewrite orTb letcc.
Qed.

Lemma lttcNge x y : lttc x y = ~~ (letc y x).
Proof. 
rewrite lttc_neqAle eq_C /letc !negb_or !negb_and.
rewrite -real_ltrNge -?real_lerNgt ?ler_eqVlt ?Creal_Re ?Creal_Im //.
have [ | | _] := (real_ltrgtP (Creal_Re x) (Creal_Re y)); rewrite //=.
by have [ | | ] := (real_ltrgtP (Creal_Im x) (Creal_Im y)).
Qed.

Lemma letcNgt x y : letc x y = ~~ (lttc y x).
Proof. by rewrite lttcNge negbK. Qed.

Lemma lttcc x : lttc x x = false.
Proof. by rewrite /lttc eq_refl /= andbF. Qed.

Lemma lttc_trans : transitive lttc.
Proof.
move=> y x z; rewrite /lttc_neqAle => /andP [le_xy _].
rewrite !lttcNge => /negP le_zy; apply/negP => le_zx.
by apply: le_zy; apply: (letc_trans le_zx le_xy).
Qed.

Lemma neq_lttc (x y : R[i]) :
  (x != y) = (lttc x y) || (lttc y x).
Proof.
rewrite !lttcNge -negb_and; congr (~~ _).
apply/idP/idP => [/eqP -> | H_anti].
  by rewrite andbb.
by rewrite eq_sym; apply/eqP; apply: letc_asym.
Qed.

Lemma eqc_letc x y : (x == y) = (letc x y && letc y x).
Proof. by apply/eqP/idP=> [->|/letc_asym]; rewrite ?letcc. Qed.

Lemma letc_total : total letc.
Proof. by move=> x y; rewrite letc_eqVlt lttcNge -orbA orNb orbT. Qed.

Lemma lttc_le_trans y x z : lttc x y -> letc y z -> lttc x z.
Proof.
move=> lt_xy; rewrite letc_eqVlt => /orP [/eqP <- // | ].
by apply: lttc_trans.
Qed.

Lemma letc_lt_trans y x z : letc x y -> lttc y z -> lttc x z.
Proof. by rewrite letc_eqVlt => /orP [/eqP <- // | ]; apply: lttc_trans. Qed.

Lemma lttc_eqF x y : lttc x y -> (x == y) = false.
Proof. by rewrite /lttc => /andP[ _ ] /negbTE. Qed.


(* Monotony of addition *)
Lemma letc_add2l x : {mono +%R x : y z / letc y z}.
Proof.
move=> y z; rewrite /letc !raddfD /= ltr_add2l ler_add2l. 
by rewrite -subr_eq0 opprD addrAC addNKr addrC subr_eq0.
Qed.

Lemma letc_add2r x : {mono +%R^~ x : y z / letc y z}.
Proof. by move=> y z /=; rewrite ![_ + x]addrC letc_add2l. Qed.

Lemma mono_inj f : {mono f : x y / letc x y} -> injective f.
Proof. by move=> mf x y /eqP; rewrite eqc_letc !mf -eqc_letc=> /eqP. Qed.

Lemma letcW_mono f : {mono f : x y / letc x y} -> {mono f : x y / lttc x y}.
Proof. by move=> mf x y; rewrite !lttc_neqAle mf (inj_eq (mono_inj mf)). Qed.

Lemma letcW_mono_Cto (R' : eqType) (f : complexR -> R') (g : rel R') :
  injective f ->
  {mono f : x y / letc x y >-> g x y} -> 
  {mono f : x y / lttc x y >-> (x != y) && g x y}.
Proof. by move=> inj_f mf x y /=; rewrite lttc_neqAle mf (inj_eq inj_f). Qed.

Lemma lttc_add2r z x y : lttc (x + z) (y + z) = lttc x y.
Proof. by rewrite (letcW_mono (letc_add2r _)). Qed.

Lemma lttc_add2l z x y : lttc (z + x) (z + y) = lttc x y.
Proof. by rewrite (letcW_mono (letc_add2l _)). Qed.

Lemma letc_add x y z t : letc x y -> letc z t -> letc (x + z) (y + t).
Proof. 
by move=> lxy lzt; rewrite (@letc_trans (y + z)) ?letc_add2l ?letc_add2r. 
Qed.

Lemma lttc_add x y z t : lttc x y -> lttc z t -> lttc (x + z) (y + t).
Proof. 
by move=> lxy lzt; rewrite (@lttc_trans (y + z)) ?lttc_add2l ?lttc_add2r. 
Qed.

Lemma letc_sum (I : Type) (r : seq I) (P : pred I) (F G : I -> complexR) :
  (forall i : I, P i -> letc (F i) (G i)) -> 
  letc (\sum_(i <- r | P i) F i) (\sum_(i <- r | P i) G i).
Proof. by exact: (big_ind2 _ (letcc _) letc_add). Qed.

(* changer l'énoncé pour la size *)
Lemma lttc_sum (I : Type) (r : seq I) (F G : I -> complexR) :
  (0 < size r)%N -> (forall i : I, lttc (F i) (G i)) -> 
  lttc (\sum_(i <- r) F i) (\sum_(i <- r) G i).
Proof.
case: r => [// | x r _ Hi]; rewrite big_cons big_cons.
apply: (@lttc_le_trans (G x + \sum_(j <- r) F j)); first by rewrite lttc_add2r.
by rewrite letc_add2l; apply: letc_sum => i _; rewrite letc_eqVlt Hi orbT.
Qed.

(* letc_iff *)
Definition letcif (x y : complexR) (C : bool) : Prop :=
    ((letc x y) * ((x == y) = C))%type.

Definition letc_of_leif x y C (le_xy : letcif x y C) := le_xy.1 : letc x y.
Coercion letc_of_leif : letcif >-> is_true.

Lemma letcifP x y C : reflect (letcif x y C) (if C then x == y else lttc x y).
Proof.
rewrite /letcif letc_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy lttc_eqF.
by move=> /orP[/eqP->|lxy] <-; rewrite ?eqxx // lttc_eqF.
Qed.

Lemma letcif_refl x C : reflect (letcif x x C) C.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.

Lemma letcif_trans x1 x2 x3 C12 C23 :
  letcif x1 x2 C12 -> letcif x2 x3 C23 -> letcif x1 x3 (C12 && C23).
Proof.
move=> ltx12 ltx23; apply/letcifP; rewrite -ltx12.
case eqx12: (x1 == x2).
  by rewrite (eqP eqx12) lttc_neqAle !ltx23 andbT; case C23.
by rewrite (@lttc_le_trans x2) ?ltx23 // lttc_neqAle eqx12 ltx12.
Qed.

Lemma letcif_le x y : letc x y -> letcif x y (letc y x).
Proof. by move=> lexy; split=> //; rewrite eqc_letc lexy. Qed.

Lemma letcif_eq x y : letc x y -> letcif x y (x == y).
Proof. by []. Qed.

Lemma getc_letcif x y C : letcif x y C -> letc y x = C.
Proof. by case=> le_xy; rewrite eqc_letc le_xy. Qed.

Lemma lttc_letcif x y C : letcif x y C -> (lttc x y) = ~~ C.
Proof. by move=> le_xy; rewrite lttc_neqAle !le_xy andbT. Qed.

Lemma mono_letcif (f : complexR -> complexR) C :
    {mono f : x y / letc x y} ->
  forall x y, (letcif (f x) (f y) C) = (letcif x y C).
Proof. by move=> mf x y; rewrite /letcif mf (inj_eq (mono_inj _)). Qed.

Lemma letcif_add x1 y1 C1 x2 y2 C2 :
    letcif x1 y1 C1 -> letcif x2 y2 C2 ->
  letcif (x1 + x2) (y1 + y2) (C1 && C2).
Proof.
rewrite -(mono_letcif _ (letc_add2r x2)) -(mono_letcif C2 (letc_add2l y1)).
exact: letcif_trans.
Qed.

Lemma letcif_sum (I : finType) (P C : pred I) (E1 E2 : I -> complexR) :
    (forall i, P i -> letcif (E1 i) (E2 i) (C i)) ->
  letcif (\sum_(i | P i) E1 i) (\sum_(i | P i) E2 i) [forall (i | P i), C i].
Proof.
move=> leE12; rewrite -big_andE.
elim/big_rec3: _ => [|i Ci m2 m1 /leE12]; first by rewrite /letcif letcc eqxx.
exact: letcif_add.
Qed.


(* max *)
Definition maxc x y := if (letc x y) then y else x.

Lemma maxcA : associative maxc.
Proof.
move=> a b c; rewrite /maxc.
case: (boolP (letc b c)) => [Hbc | /negbTE Hbc].
  case: (boolP (letc a b)) => [Hab | //].
  by rewrite Hbc (letc_trans Hab Hbc).
case: (boolP (letc a b)) => [Hab | ]; first by rewrite Hbc.  
rewrite -lttcNge => Hab; apply/eqP; rewrite eq_sym; apply/eqP.
apply: ifF; apply/negbTE; rewrite -lttcNge.
by apply: (lttc_trans _ Hab); rewrite lttcNge Hbc.
Qed.

Lemma maxc_addl : left_distributive +%R maxc.
Proof. by move=> x y z; rewrite /maxc /= letc_add2r; case: ifP => _. Qed.

Lemma maxc_addr : right_distributive +%R maxc.
Proof. by move=> x y z; rewrite ![x + _]addrC maxc_addl. Qed.

Lemma maxcc x : maxc x x = x.
Proof. by rewrite /maxc letcc. Qed.

Lemma maxcC : commutative maxc.
Proof.
move=> x y; rewrite /maxc; case: (boolP (letc x y)).
  rewrite letc_eqVlt => /orP [/eqP -> | ]; first by rewrite letcc.
  by rewrite lttcNge => /negbTE ->.
by rewrite -lttcNge lttc_neqAle => /andP[_ ->].
Qed.

Lemma maxcl x y : letc x (maxc x y).
Proof. by rewrite /maxc; case: (boolP (letc x y)). Qed.

Lemma maxcr x y : letc y (maxc x y).
Proof. by rewrite maxcC maxcl. Qed.


(* bigop pour le max pour des listes non vides ? *)
Definition bigmaxc x0 lc :=
  foldr maxc (head x0 lc) (behead lc).

Lemma bigmaxc_nil x0 : bigmaxc x0 [::] = x0.
Proof. by rewrite /bigmaxc. Qed.

Lemma bigmaxc_un x0 x :
  bigmaxc x0 [:: x] = x.
Proof. by rewrite /bigmaxc. Qed.

Lemma bigmaxc_cons x0 x y lc :
  bigmaxc x0 (x :: y :: lc) = maxc x (bigmaxc x0 (y :: lc)).
Proof.
rewrite /bigmaxc /=; elim: lc => [/= | a lc /=].
  by rewrite maxcC.
set b := foldr _ _ _; set c := foldr _ _ _ => H.
by rewrite [maxc a b]maxcC maxcA H -maxcA (maxcC c a).
Qed.

Lemma bigmaxc_letc x0 lc i :
  (i < size lc)%N -> letc (nth x0 lc i) (bigmaxc x0 lc).
Proof.
case: lc i => [i | x lc]; first by rewrite nth_nil bigmaxc_nil letcc.
elim: lc x => [x i /= | x lc /= ihlc y i i_size].
  by rewrite ltnS leqn0 => /eqP ->; rewrite nth0 bigmaxc_un /=.
rewrite bigmaxc_cons /=; case: i i_size => [_ /= | i]; first by rewrite maxcl.
rewrite ltnS /=; move/(ihlc x); move/(letc_trans)=> H; apply: H.
by rewrite maxcr.
Qed.

(* Compatibilité avec l'addition *)
Lemma bigmaxc_addr x0 lc x :
  bigmaxc (x0 + x) (map (fun y => y + x) lc) = (bigmaxc x0 lc) + x.
Proof.
case: lc => [/= | y lc]; first by rewrite bigmaxc_nil.
elim: lc y => [y | y lc ihlc z]; first by rewrite /= !bigmaxc_un.
by rewrite map_cons !bigmaxc_cons ihlc maxc_addl.
Qed.

Lemma bigmaxc_index x0 lc :
  (0 < size lc)%N -> (index (bigmaxc x0 lc) lc < size lc)%N.
Proof.
case: lc => [//= | x l _].
elim: l x => [x | x lc]; first by rewrite bigmaxc_un /= eq_refl.
move/(_ x); set z := bigmaxc _ _ => /= ihl y; rewrite bigmaxc_cons /maxc -/z.
case: (letc y z); last by rewrite eq_refl.
by case: (y == z); rewrite //.
Qed.

Lemma bigmaxc_mem x0 lc :
  (0 < size lc)%N -> bigmaxc x0 lc \in lc.
Proof. by move/(bigmaxc_index x0); rewrite index_mem. Qed.

Lemma bigmaxc_leqP x0 lc x :
  (0 < size lc)%N ->
  reflect (forall i, (i < size lc)%N -> letc (nth x0 lc i) x) (letc (bigmaxc x0 lc) x).
Proof.
move=> lc_size; apply: (iffP idP) => [le_x i i_size | H].
  by apply: (letc_trans _ le_x); apply: bigmaxc_letc.
by move/(nthP x0): (bigmaxc_mem x0 lc_size) => [i i_size <-]; apply: H.
Qed.

Lemma bigmaxcP x0 lc x :
  (x \in lc /\ forall i, (i < size lc) %N -> letc (nth x0 lc i) x) -> (bigmaxc x0 lc = x).
Proof.
move=> [] /(nthP x0) [] j j_size j_nth x_letc; apply: letc_asym; apply/andP; split.
  by apply/bigmaxc_leqP => //; apply: (leq_trans _ j_size).
by rewrite -j_nth (bigmaxc_letc _ j_size).
Qed.

(* surement à supprimer à la fin 
Lemma bigmaxc_lttc x0 lc :
  uniq lc -> forall i, (i < size lc)%N -> (i != index (bigmaxc x0 lc) lc)
    -> lttc (nth x0 lc i) (bigmaxc x0 lc).
Proof.
move=> lc_uniq Hi size_i /negP neq_i.
rewrite lttc_neqAle (bigmaxc_letc _ size_i) andbT.
apply/negP => /eqP H; apply: neq_i; rewrite -H eq_sym; apply/eqP.
by apply: index_uniq.
Qed. *)

Lemma bigmaxc_letcif x0 lc :
  uniq lc -> forall i, (i < size lc)%N ->
     letcif (nth x0 lc i) (bigmaxc x0 lc) (i == index (bigmaxc x0 lc) lc).
Proof.
move=> lc_uniq i i_size; rewrite /letcif (bigmaxc_letc _ i_size).
rewrite -(nth_uniq x0 i_size (bigmaxc_index _ (leq_trans _ i_size)) lc_uniq) //.
rewrite nth_index //.
by apply: bigmaxc_mem; apply: (leq_trans _ i_size).
Qed.


(* bigop pour le max pour des listes non vides ? *)
Definition bmaxf n (f : {ffun 'I_n.+1 -> complexR}) :=
  bigmaxc (f ord0) (codom f).

Lemma bmaxf_letc n (f : {ffun 'I_n.+1 -> complexR}) i :
  letc (f i) (bmaxf f).
Proof.
move: (@bigmaxc_letc (f ord0) (codom f) (nat_of_ord i)).
rewrite /bmaxf size_codom card_ord => H; move: (ltn_ord i); move/H.
suff -> : nth (f ord0) (codom f) i = f i; first by [].
by rewrite /codom (nth_map ord0) ?size_enum_ord // nth_ord_enum.
Qed.

Lemma bmaxf_index n (f : {ffun 'I_n.+1 -> complexR}) :
  (index (bmaxf f) (codom f) < n.+1)%N.
Proof.
rewrite /bmaxf.
have {6}-> : n.+1 = size (codom f) by rewrite size_codom card_ord.
by apply: bigmaxc_index; rewrite size_codom card_ord.
Qed.

Definition index_bmaxf n f := Ordinal (@bmaxf_index n f).

Lemma ordnat i n (ord_i : (i < n)%N) :
  i = nat_of_ord (Ordinal ord_i).
Proof. by []. Qed.

Lemma eq_index_bmaxf n (f : {ffun 'I_n.+1 -> complexR}) :
  f (index_bmaxf f) = bmaxf f.
Proof.
move: (bmaxf_index f).
rewrite -{3}[n.+1]card_ord -(size_codom f) index_mem.
move/(nth_index (f ord0)) => <-; rewrite (nth_map ord0).
  by rewrite (ordnat (bmaxf_index _)) /index_bmaxf nth_ord_enum.
by rewrite size_enum_ord; apply: bmaxf_index.
Qed.

Lemma bmaxf_letcif n (f : {ffun 'I_n.+1 -> complexR}) :
  injective f -> forall i,
     letcif (f i) (bmaxf f) (i == index_bmaxf f).
Proof.
by move=> inj_f i; rewrite /letcif bmaxf_letc -(inj_eq inj_f) eq_index_bmaxf.
Qed.

(*
Lemma bmaxf_lttc n (f : {ffun 'I_n.+1 -> complexR}) :
  injective f -> forall i, lttc (f i) (bmaxf f) = (index_bmaxf f != i).
Proof.
move=> inj_f i; rewrite /lttc bmaxf_letc andTb eq_sym.
apply/idP/idP => /negP Hneg; apply/negP => /eqP Heq; apply: Hneg; apply/eqP.
  by rewrite -eq_index_bmaxf Heq.
by apply: inj_f; rewrite eq_index_bmaxf.
Qed.
*)


(*
(* Compatibilité avec l'addition *)
Lemma bigmaxc_addr x0 lc x :
  bigmaxc (x0 + x) (map (fun y => y + x) lc) = (bigmaxc x0 lc) + x.
Proof.
case: lc => [/= | y lc]; first by rewrite bigmaxc_nil.
elim: lc y => [y | y lc ihlc z]; first by rewrite /= !bigmaxc_un.
by rewrite map_cons !bigmaxc_cons ihlc maxc_addl.
Qed.

Lemma bigmaxc_index x0 lc :
  (0 < size lc)%N -> (index (bigmaxc x0 lc) lc < size lc)%N.
Proof.
case: lc => [//= | x l _].
elim: l x => [x | x lc]; first by rewrite bigmaxc_un /= eq_refl.
move/(_ x); set z := bigmaxc _ _ => /= ihl y; rewrite bigmaxc_cons /maxc -/z.
case: (letc y z); last by rewrite eq_refl.
by case: (y == z); rewrite //.
Qed.

Lemma bigmaxc_mem x0 lc :
  (0 < size lc)%N -> bigmaxc x0 lc \in lc.
Proof. by move/(bigmaxc_index x0); rewrite index_mem. Qed.

Lemma bigmaxc_leqP x0 lc x :
  (0 < size lc)%N ->
  reflect (forall i, (i < size lc)%N -> letc (nth x0 lc i) x) (letc (bigmaxc x0 lc) x).
Proof.
move=> lc_size; apply: (iffP idP) => [le_x i i_size | H].
  by apply: (letc_trans _ le_x); apply: bigmaxc_letc.
by move/(nthP x0): (bigmaxc_mem x0 lc_size) => [i i_size <-]; apply: H.
Qed.

Lemma bigmaxcP x0 lc x :
  (x \in lc /\ forall i, (i < size lc) %N -> letc (nth x0 lc i) x) -> (bigmaxc x0 lc = x).
Proof.
move=> [] /(nthP x0) [] j j_size j_nth x_letc; apply: letc_asym; apply/andP; split.
  by apply/bigmaxc_leqP => //; apply: (leq_trans _ j_size).
by rewrite -j_nth (bigmaxc_letc _ j_size).
Qed.

Lemma bigmaxc_lttc x0 lc :
  uniq lc -> forall i, (i < size lc)%N -> (i != index (bigmaxc x0 lc) lc)
    -> lttc (nth x0 lc i) (bigmaxc x0 lc).
Proof.
move=> lc_uniq Hi size_i /negP neq_i.
rewrite lttc_neqAle (bigmaxc_letc _ size_i) andbT.
apply/negP => /eqP H; apply: neq_i; rewrite -H eq_sym; apply/eqP.
by apply: index_uniq.
Qed.*)

(* compatibilité opération produit monome : voir formule exacte *)
(* bigmax lttc ? surement mieux *)

End OrderDef.

End ComplexTotalOrder.









Section MinPoly.

Local Notation "x 'is_algebraic'" := (algebraicOver QtoC x)
  (at level 55).
 (*
Lemma poly_caract_root (F E : fieldType) (f : {rmorphism F -> E}) x : 
    algebraicOver f x -> x != 0 -> 
    {p : {poly F} | [&& p \is monic, root (map_poly f p) x & p`_0 != 0]}.
Proof.
move=> /integral_algebraic /sig2W[p pmonic proot] xneq0.
wlog p_0: p proot pmonic / p`_0 != 0=> [hwlog|]; last by exists p; apply/and3P.
have pneq0 : p != 0 by rewrite monic_neq0.
About multiplicity_XsubC.
have [n ] := multiplicity_XsubC p 0
/implyP /(_ pneq0) rootqN0 p_eq]] := multiplicity_XsubC p 0.
move: pneq0 proot pmonic.
rewrite p_eq rmorphM rootM rmorphX rmorphB rmorph0 /= map_polyX => pn0 pr pm.
have qmonic : q \is monic by move: pm; rewrite monicMr ?monic_exp ?monicXsubC.
have qn : q`_0 != 0 by rewrite -horner_coef0.
have qr : root (map_poly f q) x.
  move: pr; case: {p_eq pn0 pm} n => [|n] .
    by rewrite expr0 rootC oner_eq0 orbF.
  by rewrite rmorph0 root_exp_XsubC (negPf xneq0) orbF.
exact: (hwlog q).
Qed.*)

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

(*
Lemma psep_monic (R : fieldType) (p : {poly R}) :
  p \is monic -> psep p \is monic.
Proof.
move=> monic_p; pose p_ := gcdp p (deriv p).
have lc_neq0 : lead_coef p_ != 0.
  by rewrite lead_coef_eq0 gcdp_eq0 negb_and monic_neq0.
have p_monic : (lead_coef p_)^-1 *: p_ \is monic.
  by apply/monicP; rewrite lead_coefZ mulrC mulfV.
rewrite -(monicMr _ p_monic) /psep -/p_ -scalerCA scalerA mulrC mulfV //.
by rewrite scale1r divpK // /p_ dvdp_gcdl.
Qed.*)

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



(*
Lemma psep_coef0 (R : fieldType) (p : {poly R}) :
  p`_0 != 0 -> (psep p)`_0 != 0.
Proof.
move=> p0.
rewrite coefZ mulf_eq0 negb_or; apply/andP; split.
  rewrite lead_coef_eq0 gcdp_eq0 negb_and; apply/orP; left.
  by apply/negP => /eqP p_eq0; rewrite p_eq0 coef0 eq_refl in p0.
apply/negP => /eqP eqr; move/negP : p0; apply. 
rewrite -(divpK (dvdp_gcdl p (deriv p))) coefM big1 // => i _.
have -> : nat_of_ord i = 0%N by apply/eqP; rewrite -leqn0 -ltnS.
by rewrite eqr mul0r.
Qed.
*)
(*
Lemma poly_sep (F E : numFieldType) (f : {rmorphism F -> E}) 
  (n : nat) (P : {ffun 'I_n -> {poly F}}) (x : {ffun 'I_n -> E}) :
  (forall i, root (map_poly f (P i)) (x i)) -> 
  (forall i, P i \is monic) -> exists p : {poly F},
  [&& p \is monic, [forall i, root (map_poly f p) (x i)] & separable_poly p].
Proof.
move=> root_p monic_p.
pose r := \prod_(i < n) P i.
have r_neq0 : r != 0 by apply/prodf_neq0 => i _; rewrite monic_neq0.
have monic_r : r \is monic by apply: monic_prod.
have root_r i : root (map_poly f r) (x i).
  apply/rootPt; rewrite rmorph_prod horner_prod; apply/prodf_eq0.
  by exists i; rewrite //= (rootP (root_p i)).
pose p_ := gcdp r (deriv r); pose lc_ := (lead_coef p_).
have lc_neq0 : lc_ != 0.
  by rewrite /lc_ lead_coef_eq0 gcdp_eq0 negb_and r_neq0.
have lc_p_monic : lc_^-1 *: p_ \is monic.
  by apply/monicP; rewrite lead_coefZ mulrC mulfV.
exists (lc_ *: (r %/ p_)); apply/and3P; split.
+ rewrite -(monicMr _ lc_p_monic) -scalerCA scalerA mulrC mulfV //.
  by rewrite scale1r divpK // /p_ dvdp_gcdl.
+ apply/forallP => i; rewrite map_polyZ; apply/rootP/eqP. 
  rewrite hornerZ mulf_eq0; apply/orP; right; apply/eqP/rootP.
  move: (divpK (dvdp_gcdl r (deriv r))); rewrite -/p_ => eq_p.
  rewrite -mu_gt0; last first.
    rewrite map_poly_eq0; apply/negP => /eqP H; rewrite H mul0r in eq_p.
    by rewrite -eq_p eq_refl in r_neq0.
  have rp_neq0 : (map_poly f (r %/ p_)) * (map_poly f p_) != 0. 
    by rewrite -rmorphM eq_p map_poly_eq0.
  rewrite -(ltn_add2r (\mu_(x i) (map_poly f p_))) add0n -mu_mul //.
  rewrite -rmorphM /= divpK ?dvdp_gcdl //.
  rewrite (mu_deriv_root _ (root_r i)) ?map_poly_eq0 // addn1 ltnS /p_ /=. 
  rewrite gcdp_map deriv_map /=.
  have H := (divpK (dvdp_gcdr (map_poly f r) (map_poly f r^`()))).
  rewrite -{2}H mu_mul ?leq_addl // H -size_poly_eq0 -deriv_map size_deriv.
  rewrite -lt0n -ltnS prednK; last by rewrite lt0n size_poly_eq0 map_poly_eq0.
  by apply: (root_size_gt1 _ (root_r i)); rewrite map_poly_eq0.
+ by rewrite separable_polyZ ?make_separable.
Qed.
*)

Lemma ratr_eq0 (x : rat) : ((QtoC x) == (0: complexR)) = (x == 0).
Proof.
by rewrite -numq_eq0 mulf_eq0 invr_eq0 !intr_eq0 (negbTE (denq_neq0 x)) orbF.
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

(*
Lemma poly_caract_int (x : complexR) : x is_algebraic -> x != 0 ->
    exists p : {poly int}, [&& (p != 0), root (map_poly ZtoC p) x,
    (p`_0 != 0), (0 < lead_coef p) & separable_poly (map_poly ZtoC p)].
Proof.
move => algebraic_x xn0.
have [r /andP[monr /andP[rootr r0_neq0]]] := (poly_caract_root algebraic_x xn0).
have monp := (psep_monic monr).
have rootp := (psep_root (monic_neq0 monr) rootr).
have p0_neq0 := (psep_coef0 r0_neq0).
have sepp := (psep_separable (monic_neq0 monr)).
have : {q : {poly int} & {a : int_ZmodType | (0 < a) 
     & psep r = a%:~R^-1 *: map_poly (intr : int -> rat) q}}.
  have [p_ [a /negbTE a_neq0 eq_p_p_]] := rat_poly_scale (psep r).
  have [a_gt0 | a_le0 | /eqP] := (ltrgt0P a); last by rewrite a_neq0.
    by exists p_; exists a.
  exists (- p_); exists (- a); rewrite ?oppr_gt0 //.
  by rewrite !rmorphN invrN /= scaleNr scalerN opprK.
move=> [p_ [a a_gt0 eq_p_p_]].
have a_neq0 : ratr a%:~R != 0 :> complexR.
  by rewrite ratr_int intr_eq0 lt0r_neq0.    
have p_0_neq0 : p_`_0 != 0.
  apply/negP => /eqP p_eq0; move/negP: p0_neq0; apply.
  by rewrite eq_p_p_ coefZ coef_map p_eq0 mulr0.
have p__neq0 : p_ != 0.
  by apply/negP => /eqP p__eq0; move/negP: p_0_neq0; rewrite p__eq0 coef0.
have eq_p__p : (map_poly intr p_) = a%:~R *: (psep r).
  by rewrite eq_p_p_ scalerA mulfV ?scale1r // intr_eq0; apply: lt0r_neq0. 
have lc_p_gt0 : (0 < (lead_coef p_)).
  have H : (lead_coef p_)%:~R = a%:~R * lead_coef (psep r).
    rewrite eq_p_p_ lead_coefZ lead_coef_map_eq ?intr_eq0 ?lead_coef_eq0 //.
    by rewrite mulrA mulfV ?mul1r // intr_eq0; apply: (lt0r_neq0 a_gt0).
  by rewrite -(ltr0z rat_numDomainType) H (monicP monp) mulr1 ltr0z. 
have ZtoQtoC : QtoC \o intr =1 ZtoC by move=> y /=; rewrite ratr_int.
have root_map_p : root (map_poly intr p_) x.
  by rewrite -(eq_map_poly ZtoQtoC) map_poly_comp eq_p__p map_polyZ /= rootZ.
exists p_; apply/and5P; split; rewrite //. 
rewrite -(eq_map_poly ZtoQtoC) map_poly_comp eq_p__p map_polyZ /=.
by rewrite (separable_polyZ _ a_neq0) separable_map.
Qed.*)
(*
Lemma polyMinZ_subproof (x : complexR) : x is_algebraic -> x != 0 -> 
    {p : {poly int} | [&& (p != 0), root (map_poly ZtoC p) x,
    (p`_0 != 0), (0 < lead_coef p) & separable_poly (map_poly ZtoC p)]}.
Proof.
move => x_alg x_neq0.
have [p /and5P] := (sigW (poly_caract_int x_alg x_neq0)).
move => [p_neq0 rootp p0_neq0 lc_gt0 p_sep].
exists p; apply/and5P; split; rewrite ?p_sep ?andbT //.
Qed.

Definition polyMinZ (x : complexR) (H : x is_algebraic) := 
  match Sumbool.sumbool_of_bool(x != 0) with
  |right _ => 'X
  |left toto => sval(polyMinZ_subproof H toto) 
  end.
*)

Definition polyMinZ (x : complexR) (H : x is_algebraic) :=
  sval (poly_caract_int H).

Definition polyMin (x : complexR) (H : x is_algebraic) :=
  map_poly ZtoC (polyMinZ H).

(*
+ by rewrite map_poly_eq0_id0 ?intr_eq0 ?(lt0r_neq0 lc_gt0).
+ by apply/polyOverP => i; rewrite coef_map /= Cint_int.
+ by rewrite coef_map intr_eq0.
by rewrite lead_coef_map_eq ?intr_eq0 ?ltr0z ?lt0r_neq0.
Qed.
*)

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

Lemma polyMinZ_root (x : complexR) (H : x is_algebraic) : 
  root (map_poly ZtoC (polyMinZ H)) x.
Proof.
move: (svalP (poly_caract_int H)) => [_ _ _ ->].
by rewrite dvdpp.
Qed.

Lemma polyMin_root (x : complexR) (H : x is_algebraic) : 
  root (polyMin H) x.
Proof. by rewrite polyMinZ_root. Qed.

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

(*
Lemma polyMinZ_coef0_neq0 (x : complexR) (H : x is_algebraic) :
  ((polyMinZ H)`_0 == 0) = (x == 0).
Proof.
rewrite /polyMinZ.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | /eqP ->]; last first.
  by rewrite coefX eq_refl.
move: (svalP (polyMinZ_subproof H a)) => /and5P[_ _ /negbTE -> _ _].
by apply: esym; apply/negP /negP.
Qed.

Lemma polyMin_coef0_neq0 (x : complexR) (H : x is_algebraic) :
  ((polyMin H)`_0 == 0) = (x == 0).
Proof.
by rewrite coef_map intr_eq0 polyMinZ_coef0_neq0.
Qed.
*)

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



(*
Print coprimep.
Pdiv.CommonIdomain.eqp_dvdl:
  forall (R : idomainType) (d2 d1 p : {poly R}), d1 %= d2 -> (d1 %| p) = (d2 %| p)

dvdp_rat_int: forall p q : {poly int_Ring}, (map_poly ZtoQ p %| map_poly ZtoQ q) = (p %| q)
Search _ gcdp.
Search _ size 1%N.
mul_polyC: forall (R : ringType) (a : R) (p : {poly R}), a%:P * p = a *: p
size1_polyC: forall (R : ringType) (p : {poly R}), (size p <= 1)%N -> p = (p`_0)%:P
dvdp_gcd_idr: forall (R : idomainType) (m n : {poly R}), n %| m -> gcdp m n %= n
leq_gcdpr: forall (R : idomainType) (p q : {poly R}), q != 0 -> (size (gcdp p q) <= size q)%N
separable_root:
  forall (R : idomainType) (p : {poly R}) (x : R),
  separable_poly (p * ('X - x%:P)) = separable_poly p && ~~ root p x


irredp_XsubC: forall (R : idomainType) (x : R), irreducible_poly ('X - x%:P)
poly2_root: forall (F : fieldType) (p : {poly F}), size p = 2 -> {r : F | root p r}

About poly_caract_int.

About algebraic0.
About sigW.
Check (sigW (poly_caract_int (algebraic0 (ratr_rmorphism complexR_numFieldType)))).
*)

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


(*
Lemma polyMin_subproof (x : complexR) : x is_algebraic -> x != 0 -> 
    {p : {poly int} | [&& (p != 0), root (map_poly ZtoC p) x,
    (p`_0 != 0), (0 < lead_coef p) & separable_poly (map_poly ZtoC p)]}.
Proof.
move => x_alg x_neq0.
have [p /and5P] := (sigW (poly_caract_int x_alg x_neq0)).
move => [p_neq0 rootp p0_neq0 lc_gt0 p_sep].
by exists p; rewrite p_neq0 rootp p0_neq0 lc_gt0 p_sep.
Qed.

Definition polyMin (x : complexR) (H : x is_algebraic) :=
  match Sumbool.sumbool_of_bool(x != 0) with
  |right _ => 'X
  |left toto => sval(polyMin_subproof H toto) 
  end.

Lemma polyMin_neq0 (x : complexR) (H : x is_algebraic) : (polyMin H) != 0.
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | _]; last first.
  by rewrite polyX_eq0.
by move: (svalP (polyMin_subproof H a)) => /and5P[].
Qed.

Lemma polyMin_root (x : complexR) (H : x is_algebraic) : 
  root (map_poly ZtoC (polyMin H)) x.
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | /eqP ->]; last first.
  by rewrite map_polyX rootX.
by move: (svalP (polyMin_subproof H a)) => /and5P[].
Qed.

Lemma polyMin_lcoef_gt0 (x : complexR) (H : x is_algebraic) : 
  0 < lead_coef (polyMin H).
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | _]; last first.
  by rewrite lead_coefX.
by move: (svalP (polyMin_subproof H a)) => /and5P[].
Qed.

Lemma polyMin_coef0_neq0 (x : complexR) (H : x is_algebraic) :
  ((polyMin H)`_0 == 0) = (x == 0).
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | /eqP ->]; last first.
  by rewrite coefX eq_refl.
move: (svalP (polyMin_subproof H a)) => /and5P[_ _ /negbTE -> _ _].
by apply/eqP; rewrite eq_sym; apply/eqP/negbTE; rewrite a.
Qed.

Lemma polyMin_separable (x : complexR) (H : x is_algebraic) :
  separable_poly (map_poly ZtoC (polyMin H)).
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | _]; last first.
  by rewrite /separable_poly deriv_map derivX rmorph1 coprimep1.
by move: (svalP (polyMin_subproof H a)) => /and5P[].
Qed.

*)






End MinPoly.






(* Inutile ici ?
Lemma Euler :
  1 + Cexp (PI%:C * 'i) = 0.
Proof.
rewrite /Cexp ImiRe ReiNIm -complexr0 /= cos_PI sin_PI !complexr0.
rewrite oppr0 exp_0 mul1r; apply/eqP.
by rewrite eq_complex /= addr0 addrN eq_refl.
Qed. *)

(* Utile ?
Lemma ReM (x : complexR) y :
  Re_R (x * (RtoC y)) = (Re_R x) * y.
Proof. by rewrite real_complexE; case: x => r i /=; rewrite !C_simpl. Qed.

Lemma ImM (x : complexR) y :
  Im (x * y%:C) = (Im x) * y.
Proof.
rewrite real_complexE; case: x => r i.
by rewrite mulcalc /= mulr0 add0r.
Qed.

Lemma ReX (y : R) n :
  Re (y%:C ^+ n) = y ^+ n.
Proof.
elim: n => [| n Ihn].
  by rewrite !expr0 /=.  
by rewrite !exprS mulrC ReM Ihn mulrC.
Qed.

Lemma ImX (y : R) n :
  Im (y%:C ^+ n) = 0.
Proof.
elim: n => [| n Ihn].
  by rewrite !expr0 /=.  
by rewrite !exprS mulrC ImM Ihn mul0r.
Qed. *)