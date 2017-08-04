From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import poly ssrint rat.
From mathcomp Require Import complex mxpoly fieldext polyorder polydiv algC.
From mathcomp Require Import matrix vector falgebra countalg.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Module Archi.

Local Notation num_for T b := (@Num.NumDomain.Pack T b T).

Module ArchiNumDomain.

Section ClassDef.

Record class_of R :=
  Class {base : Num.NumDomain.class_of R; _ : @Num.archimedean_axiom (num_for R base)}.
Local Coercion base : class_of >-> Num.NumDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition clone c of phant_id class c := @Pack T c T.
Definition pack b0 (m0 : Num.archimedean_axiom (num_for T b0)) :=
  fun bT b & phant_id (Num.NumDomain.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.NumDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Notation archiNumDomainType := type.
Notation ArchiNumDomainType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'archiNumDomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'archiNumDomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'archiNumDomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'archiNumDomainType'  'of'  T ]") : form_scope.
End Exports.

End ArchiNumDomain.
Import ArchiNumDomain.Exports.

Module ArchiNumField.

Section ClassDef.

Record class_of R :=
  Class { base : Num.NumField.class_of R; mixin : @Num.archimedean_axiom (num_for R base) }.
Definition base2 R (c : class_of R) := ArchiNumDomain.Class (@mixin R c).
Local Coercion base : class_of >-> Num.NumField.class_of.
Local Coercion base2 : class_of >-> ArchiNumDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (Num.NumField.class bT) (b : Num.NumField.class_of T) =>
  fun mT m & phant_id (ArchiNumDomain.class mT) (@ArchiNumDomain.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition archiNumDomainType := @ArchiNumDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition numFieldType := @Num.NumField.Pack cT xclass xT.
Definition join_archiNumDomainType := @ArchiNumDomain.Pack numFieldType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.NumField.class_of.
Coercion base2 : class_of >-> ArchiNumDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Coercion archiNumDomainType : type >-> ArchiNumDomain.type.
Canonical archiNumDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> Num.NumField.type.
Canonical numFieldType.
Canonical join_archiNumDomainType.
Notation archiNumFieldType := type.
Notation "[ 'archiNumFieldType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiNumFieldType'  'of'  T ]") : form_scope.
End Exports.

End ArchiNumField.
Import ArchiNumField.Exports.

Module ArchiNumClosedField.

Section ClassDef.

Record class_of R :=
  Class { base : Num.ClosedField.class_of R; mixin : @Num.archimedean_axiom (num_for R base) }.
Definition base2 R (c : class_of R) := ArchiNumField.Class (@mixin R c).
Local Coercion base : class_of >-> Num.ClosedField.class_of.
Local Coercion base2 : class_of >-> ArchiNumField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (Num.ClosedField.class bT) (b : Num.ClosedField.class_of T) =>
  fun mT m & phant_id (ArchiNumDomain.class mT) (@ArchiNumDomain.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition archiNumDomainType := @ArchiNumDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition numFieldType := @Num.NumField.Pack cT xclass xT.
Definition archiNumFieldType := @ArchiNumField.Pack cT xclass xT.
Definition closedFieldType := @GRing.ClosedField.Pack cT xclass xT.
Definition numClosedFieldType := @Num.ClosedField.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.ClosedField.class_of.
Coercion base2 : class_of >-> ArchiNumField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Coercion archiNumDomainType : type >-> ArchiNumDomain.type.
Canonical archiNumDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> Num.NumField.type.
Canonical numFieldType.
Coercion archiNumFieldType : type >-> ArchiNumField.type.
Canonical archiNumFieldType.
Coercion closedFieldType : type >-> GRing.ClosedField.type.
Canonical closedFieldType.
Coercion numClosedFieldType : type >-> Num.ClosedField.type.
Canonical numClosedFieldType.
Notation archiNumClosedFieldType := type.
Notation "[ 'archiNumClosedFieldType' 'of' T ]" :=  (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiNumClosedFieldType'  'of'  T ]") : form_scope.
End Exports.

End ArchiNumClosedField.
Import ArchiNumClosedField.Exports.

Module ArchiRealDomain.

Section ClassDef.

Record class_of R :=
  Class {base : Num.RealDomain.class_of R; mixin : @Num.archimedean_axiom (num_for R base)}.
Definition base2 R (c : class_of R) := ArchiNumDomain.Class (@mixin R c).
Local Coercion base : class_of >-> Num.RealDomain.class_of.
Local Coercion base2 : class_of >-> ArchiNumDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (Num.RealDomain.class bT) (b : Num.RealDomain.class_of T) =>
  fun mT m & phant_id (ArchiNumDomain.class mT) (@ArchiNumDomain.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition archiNumDomainType := @ArchiNumDomain.Pack cT xclass xT.
Definition realDomainType := @Num.RealDomain.Pack cT xclass xT.
Definition join_archiNumDomainType := @ArchiNumDomain.Pack realDomainType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.RealDomain.class_of.
Coercion base2 : class_of >-> ArchiNumDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Coercion realDomainType : type >-> Num.RealDomain.type.
Canonical realDomainType.
Coercion archiNumDomainType : type >-> ArchiNumDomain.type.
Canonical archiNumDomainType.
Canonical join_archiNumDomainType.
Notation archiRealDomainType := type.
Notation "[ 'archiRealDomainType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiRealDomainType'  'of'  T ]") : form_scope.
End Exports.

End ArchiRealDomain.
Import ArchiRealDomain.Exports.

Module ArchiRealField.

Section ClassDef.

Record class_of R :=
  Class { base : Num.RealField.class_of R; mixin : @Num.archimedean_axiom (num_for R base) }.
Definition base2 R (c : class_of R) := ArchiNumField.Class (@mixin R c).
Local Coercion base : class_of >-> Num.RealField.class_of.
Definition base3 R (c : class_of R) := @ArchiRealDomain.Class _ c (@mixin _ c). (* TODO : order *)
Local Coercion base2 : class_of >-> ArchiNumField.class_of.
Local Coercion base3 : class_of >-> ArchiRealDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (Num.RealField.class bT) (b : Num.RealField.class_of T) =>
  fun mT m & phant_id (ArchiNumDomain.class mT) (@ArchiNumDomain.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition realDomainType := @Num.RealDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition numFieldType := @Num.NumField.Pack cT xclass xT.
Definition realFieldType := @Num.RealField.Pack cT xclass xT.
Definition archiNumDomainType := @ArchiNumDomain.Pack cT xclass xT.
Definition archiNumFieldType := @ArchiNumField.Pack cT xclass xT.
Definition archiRealDomainType := @ArchiRealDomain.Pack cT xclass xT.
Definition join_archiNumFieldType := @ArchiNumField.Pack numFieldType xclass xT.
Definition join_archiRealDomainType := @ArchiRealDomain.Pack realDomainType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.RealField.class_of.
Coercion base2 : class_of >-> ArchiNumField.class_of.
Coercion base3 : class_of >-> ArchiRealDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Coercion archiNumDomainType : type >-> ArchiNumDomain.type.
Canonical archiNumDomainType.
Coercion realDomainType : type >-> Num.RealDomain.type.
Canonical realDomainType.
Coercion archiRealDomainType : type >-> ArchiRealDomain.type.
Canonical archiRealDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> Num.NumField.type.
Canonical numFieldType.
Coercion archiNumFieldType : type >-> ArchiNumField.type.
Canonical archiNumFieldType.
Coercion realFieldType : type >-> Num.RealField.type.
Canonical realFieldType.
Canonical join_archiNumFieldType.
Canonical join_archiRealDomainType.
Notation archiRealFieldType := type.
Notation "[ 'archiRealFieldType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiRealFieldType'  'of'  T ]") : form_scope.
End Exports.

End ArchiRealField.
Import ArchiRealField.Exports.

Module ArchiRealClosedField.

Section ClassDef.

Record class_of R :=
  Class { base : Num.RealClosedField.class_of R; mixin : @Num.archimedean_axiom (num_for R base) }.
Definition base2 R (c : class_of R) := ArchiRealField.Class (@mixin R c).
Local Coercion base : class_of >-> Num.RealClosedField.class_of.
Local Coercion base2 : class_of >-> ArchiRealField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (Num.RealClosedField.class bT) (b : Num.RealClosedField.class_of T) =>
  fun mT m & phant_id (ArchiNumDomain.class mT) (@ArchiNumDomain.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition archiNumDomainType := @ArchiNumDomain.Pack cT xclass xT.
Definition realDomainType := @Num.RealDomain.Pack cT xclass xT.
Definition archiRealDomainType := @ArchiRealDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition numFieldType := @Num.NumField.Pack cT xclass xT.
Definition archiNumFieldType := @ArchiNumField.Pack cT xclass xT.
Definition realFieldType := @Num.RealField.Pack cT xclass xT.
Definition archiRealFieldType := @ArchiRealField.Pack cT xclass xT.
Definition realClosedFieldType := @Num.RealClosedField.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.RealClosedField.class_of.
Coercion base2 : class_of >-> ArchiRealField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Coercion archiNumDomainType : type >-> ArchiNumDomain.type.
Canonical archiNumDomainType.
Coercion realDomainType : type >-> Num.RealDomain.type.
Canonical realDomainType.
Coercion archiRealDomainType : type >-> ArchiRealDomain.type.
Canonical archiRealDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> Num.NumField.type.
Canonical numFieldType.
Coercion realFieldType : type >-> Num.RealField.type.
Canonical realFieldType.
Coercion archiNumFieldType : type >-> ArchiNumField.type.
Canonical archiNumFieldType.
Coercion archiRealFieldType : type >-> ArchiRealField.type.
Canonical archiRealFieldType.
Coercion realClosedFieldType : type >-> Num.RealClosedField.type.
Canonical realClosedFieldType.
Notation archiRcfType := type.
Notation "[ 'archiRcfType' 'of' T ]" :=  (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiRcfType'  'of'  T ]") : form_scope.
End Exports.

End ArchiRealClosedField.
Import ArchiRealClosedField.Exports.

Module Import Internals.

Fact archi_bound_subproof (R : archiNumDomainType) : Num.archimedean_axiom R.
Proof. by case: R => ? []. Qed.

End Internals.

Module Import ExtraDef.

Definition archi_bound {R} x := sval (sigW (@archi_bound_subproof R x)).

End ExtraDef.

Notation bound := archi_bound.

Module Theory.

Section ArchiNumTheory.

Variables (R : archiNumDomainType) (x : R).

Lemma archi_boundP : 0 <= x -> x < (bound x)%:R.
Proof. by move/ger0_norm=> {1}<-; rewrite /bound; case: (sigW _). Qed.

End ArchiNumTheory.

Section ArchiRealTheory.

Variables (R : archiRealDomainType) (x : R).

Lemma upper_nthrootP i : (bound x <= i)%N -> x < 2%:R ^+ i.
Proof. 
rewrite /bound; case: (sigW _) => /= b le_x_b le_b_i.
apply: (ler_lt_trans (ler_norm _) (ltr_trans le_x_b _ )).
by rewrite -natrX ltr_nat (leq_ltn_trans le_b_i) // ltn_expl.
Qed.

End ArchiRealTheory.

Section ArchiNumDomainTheory.

Variable R : archiNumDomainType.
Implicit Types x y z : R.
Implicit Type nu : {rmorphism R -> R}.

(*    nat subset     *)

Section CnatTheory.

Implicit Types m n : nat.

Fact truncC_subproof x : {m | (0 <= x)-> (m%:R <= x < m.+1%:R) }.
Proof.
have [Rx | _] := boolP (0 <= x); last by exists 0%N.
have /ex_minnP[n lt_x_n1 min_n]: exists n, x < n.+1%:R; last first.
  exists n ; rewrite lt_x_n1 andbT.
  case Dn: n => // [n1]; rewrite -Dn.
  have [//|]:= (real_lerP (rpred_nat _ n) (ger0_real Rx)).
  by rewrite Dn => /min_n; rewrite Dn ltnn.
exists (archi_bound x).
by apply: (ltr_trans (archi_boundP Rx)); rewrite ltr_nat.
Qed.

Definition truncC x := if 0 <= x then sval (truncC_subproof x) else 0%N.
Definition Cnat := Qualifier 1 (fun x : R => (truncC x)%:R == x).

Fact Cnat_key : pred_key Cnat. Proof. by []. Qed.
Canonical Cnat_keyed := KeyedQualifier Cnat_key.

Lemma truncC_itv x : 0 <= x -> (truncC x)%:R <= x < (truncC x).+1%:R.
Proof.
move => x_ge0; rewrite /truncC ifT //.
by case: (truncC_subproof x) => /= m; move/(_ x_ge0).
Qed.

Lemma truncC_def x n : n%:R <= x < n.+1%:R -> truncC x = n.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eqn_leq -ltnS -[(n <= _)%N]ltnS.
have /truncC_itv/andP[lefx ltxf1]: x >= 0.
  by apply: (ler_trans _ lemx); apply: ler0n.
by rewrite -!(ltr_nat R) 2?(@ler_lt_trans _ x).
Qed.

Lemma natCK : cancel (GRing.natmul 1) truncC.
Proof. by move=> m; apply: truncC_def; rewrite ler_nat ltr_nat ltnS leqnn. Qed.

Lemma truncCK : {in Cnat, cancel truncC (GRing.natmul 1)}.
Proof. by move=> x /eqP. Qed.

Lemma truncC0 : truncC 0 = 0%N. Proof. exact: (natCK 0%N). Qed.
Lemma truncC1 : truncC 1 = 1%N. Proof. exact: (natCK 1%N). Qed.
Hint Resolve truncC0 truncC1.

Lemma CnatP x : reflect (exists n, x = n%:R) (x \is a Cnat).
Proof.
by apply: (iffP eqP) => [<- | [n ->]]; [exists (truncC x) | rewrite natCK].
Qed.

Lemma Cnat_nat n : n%:R \is a Cnat. Proof. by apply/CnatP; exists n. Qed.
Hint Resolve Cnat_nat.

Lemma truncCD :
  {in Cnat & Num.nneg, {morph truncC : x y / x + y >-> (x + y)%N}}.
Proof.
move=> _ y /CnatP[n ->] y_ge0; apply: truncC_def.
by rewrite -addnS !natrD !natCK ler_add2l ltr_add2l truncC_itv.
Qed.

Lemma truncCM : {in Cnat &, {morph truncC : x y / x * y >-> (x * y)%N}}.
Proof. by move=> _ _ /CnatP[n1 ->] /CnatP[n2 ->]; rewrite -natrM !natCK. Qed.

Lemma truncCX n : {in Cnat, {morph truncC : x / x ^+ n >-> (x ^ n)%N}}.
Proof. by move=> _ /CnatP[n1 ->]; rewrite -natrX !natCK. Qed.

Lemma rpred_Cnat S (ringS : semiringPred S) (kS : keyed_pred ringS) x :
  x \is a Cnat -> x \in kS.
Proof. by case/CnatP=> n ->; apply: rpred_nat. Qed.

Lemma Cnat0 : 0 \is a Cnat. Proof. exact: (Cnat_nat 0). Qed.
Lemma Cnat1 : 1 \is a Cnat. Proof. exact: (Cnat_nat 1). Qed.
Hint Resolve Cnat0 Cnat1.

Fact Cnat_semiring : semiring_closed Cnat.
Proof.
by do 2![split] => //= _ _ /CnatP[n ->] /CnatP[m ->]; rewrite -(natrD, natrM).
Qed.
Canonical Cnat_addrPred := AddrPred Cnat_semiring.
Canonical Cnat_mulrPred := MulrPred Cnat_semiring.
Canonical Cnat_semiringPred := SemiringPred Cnat_semiring.

Lemma real_Cnat : {subset Cnat <= Num.real}.
Proof. move=> _ /CnatP[m ->]; apply: realn. Qed.

Lemma Cnat_normK x : x \is a Cnat -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/real_Cnat/real_normK. Qed.

Lemma truncC_gt0 x : (0 < truncC x)%N = (1 <= x).
Proof.
apply/idP/idP=> [m_gt0 | x_ge1].
  have /truncC_itv/andP[lemx _]: 0 <= x.
    by move: m_gt0; rewrite /truncC; case: ifP.
  by apply: ler_trans lemx; rewrite ler1n.
have /truncC_itv/andP[_ ltxm1]:= ler_trans ler01 x_ge1.
by rewrite -ltnS -(ltr_nat R) (ler_lt_trans x_ge1).
Qed.

Lemma truncC0Pn x : reflect (truncC x = 0%N) (~~ (1 <= x)).
Proof. by rewrite -truncC_gt0 -eqn0Ngt; apply: eqP. Qed.

Lemma Cnat_ge0 x : x \is a Cnat -> 0 <= x.
Proof. by case/CnatP=> n ->; apply: ler0n. Qed.

Lemma Cnat_gt0 x : x \is a Cnat -> (0 < x) = (x != 0).
Proof. by case/CnatP=> n ->; rewrite pnatr_eq0 ltr0n lt0n. Qed.

Lemma norm_Cnat x : x \is a Cnat -> `|x| = x.
Proof. by move/Cnat_ge0/ger0_norm. Qed.

Lemma Cnat_sum_eq1 (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> F i \is a Cnat) -> \sum_(i | P i) F i = 1 ->
   {i : I | [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]}.
Proof.
move=> natF sumF1; pose nF i := truncC (F i).
have{natF} defF i: P i -> F i = (nF i)%:R by move/natF/eqP.
have{sumF1} /eqP sumF1: (\sum_(i | P i) nF i == 1)%N.
  by rewrite -(@eqr_nat R) natr_sum -(eq_bigr _ defF) sumF1.
have [i Pi nZfi]: {i : I | P i & nF i != 0%N}.
  by apply/sig2W/exists_inP; rewrite -negb_forall_in -sum_nat_eq0 sumF1.
have F'ge0 := (leq0n _, etrans (eq_sym _ _) (sum_nat_eq0 (predD1 P i) nF)).
rewrite -lt0n in nZfi; have [_] := (leqif_add (leqif_eq nZfi) (F'ge0 _)).
rewrite /= big_andbC -bigD1 // sumF1 => /esym/andP/=[/eqP Fi1 /forall_inP Fi'0].
exists i; split=> // [|j neq_ji Pj]; first by rewrite defF // -Fi1.
by rewrite defF // (eqP (Fi'0 j _)) // neq_ji.
Qed.

Lemma Cnat_mul_eq1 x y :
  x \is a Cnat -> y \is a Cnat -> (x * y == 1) = (x == 1) && (y == 1).
Proof. by do 2!move/truncCK <-; rewrite -natrM !pnatr_eq1 muln_eq1. Qed.

Lemma Cnat_prod_eq1 (I : finType) (P : pred I) (F : I -> R) :
    (forall i, P i -> F i \is a Cnat) -> \prod_(i | P i) F i = 1 ->
  forall i, P i -> F i = 1.
Proof.
move=> natF prodF1; apply/eqfun_inP; rewrite -big_andE.
move: prodF1; elim/(big_load (fun x => x \is a Cnat)): _.
elim/big_rec2: _ => // i all1x x /natF N_Fi [Nx x1all1].
by split=> [|/eqP]; rewrite ?rpredM ?Cnat_mul_eq1 // => /andP[-> /eqP].
Qed.

(* predCmod *)
Variables (U V : lmodType R) (f : {additive U -> V}).

Lemma raddfZ_Cnat a u : a \is a Cnat -> f (a *: u) = a *: f u. 
Proof. by case/CnatP=> n ->; apply: raddfZnat. Qed.

Lemma rpredZ_Cnat S (addS : @addrPred V S) (kS : keyed_pred addS) :
  {in Cnat & kS, forall z u, z *: u \in kS}.
Proof. by move=> _ u /CnatP[n ->]; apply: rpredZnat. Qed.

(* autC *)
Lemma aut_Cnat nu : {in Cnat, nu =1 id}.
Proof. by move=> _ /CnatP[n ->]; apply: rmorph_nat. Qed.

End CnatTheory.

(*     int subset      *)

Section CintTheory.

Implicit Types m : int.

Fact floorC_subproof x : {m | x \is Num.real -> intr m <= x < intr (m + 1)}.
Proof.
have [Rx | _] := boolP (x \is Num.real); last by exists 0.
without loss x_ge0: x Rx / x >= 0.
  have [x_ge0 | /ltrW x_le0] := real_ger0P Rx; first exact.
  case/(_ (- x)) => [||m /(_ isT)]; rewrite ?rpredN ?oppr_ge0 //.
  rewrite ler_oppr ltr_oppl -!rmorphN opprD /= ltr_neqAle ler_eqVlt.
  case: eqP => [-> _ | _ /and3P[lt_x_m _ le_m_x]].
    by exists (- m) => _; rewrite lerr rmorphD ltr_addl ltr01.
  by exists (- m - 1); rewrite le_m_x subrK.
exists (Posz (truncC x)) => _ ; rewrite addrC -intS -!natz !mulrz_nat.
exact: (truncC_itv x_ge0).
Qed.

Definition floorC x := sval (floorC_subproof x).
Definition Cint := [qualify a x : R | (floorC x)%:~R == x].

Fact Cint_key : pred_key Cint. Proof. by []. Qed.
Canonical Cint_keyed := KeyedQualifier Cint_key.

Lemma floorC_itv x : x \is Num.real -> (floorC x)%:~R <= x < (floorC x + 1)%:~R.
Proof. by rewrite /floorC => Rx; case: (floorC_subproof x) => //= m; apply. Qed.

Lemma floorC_def x m : m%:~R <= x < (m + 1)%:~R -> floorC x = m.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eqr_le -!ltz_addr1.
have /floorC_itv/andP[lefx ltxf1]: x \is Num.real.
  by rewrite -[x](subrK m%:~R) rpredD ?realz ?ler_sub_real.
by rewrite -!(ltr_int R) 2?(@ler_lt_trans _ x).
Qed.

Lemma intCK : cancel intr floorC.
Proof.
by move=> m; apply: floorC_def; rewrite ler_int ltr_int ltz_addr1 lerr.
Qed.

Lemma floorCK : {in Cint, cancel floorC intr}. Proof. by move=> z /eqP. Qed.

Lemma floorC0 : floorC 0 = 0. Proof. exact: (intCK 0). Qed.
Lemma floorC1 : floorC 1 = 1. Proof. exact: (intCK 1). Qed.
Hint Resolve floorC0 floorC1.

Lemma floorCpK (p : {poly R}) :
  p \is a polyOver Cint -> map_poly intr (map_poly floorC p) = p.
Proof.
move/(all_nthP 0)=> Zp; apply/polyP=> i.
rewrite coef_map coef_map_id0 //= -[p]coefK coef_poly.
by case: ifP => [/Zp/floorCK // | _]; rewrite floorC0.
Qed.

Lemma floorCpP (p : {poly R}) :
  p \is a polyOver Cint -> {q | p = map_poly intr q}.
Proof. by exists (map_poly floorC p); rewrite floorCpK. Qed.

Lemma Cint_int m : m%:~R \is a Cint.
Proof. by rewrite unfold_in intCK. Qed.

Lemma CintP x : reflect (exists m, x = m%:~R) (x \is a Cint).
Proof.
by apply: (iffP idP) => [/eqP<-|[m ->]]; [exists (floorC x) | apply: Cint_int].
Qed.

Lemma floorCD : {in Cint & Num.real, {morph floorC : x y / x + y}}.
Proof.
move=> _ y /CintP[m ->] Ry; apply: floorC_def.
by rewrite -addrA 2!rmorphD /= intCK ler_add2l ltr_add2l floorC_itv.
Qed.

Lemma floorCN : {in Cint, {morph floorC : x / - x}}.
Proof. by move=> _ /CintP[m ->]; rewrite -rmorphN !intCK. Qed.

Lemma floorCM : {in Cint &, {morph floorC : x y / x * y}}.
Proof. by move=> _ _ /CintP[m1 ->] /CintP[m2 ->]; rewrite -rmorphM !intCK. Qed.

Lemma floorCX n : {in Cint, {morph floorC : x / x ^+ n}}.
Proof. by move=> _ /CintP[m ->]; rewrite -rmorphX !intCK. Qed.

Lemma rpred_Cint S (ringS : subringPred S) (kS : keyed_pred ringS) x :
  x \is a Cint -> x \in kS.
Proof. by case/CintP=> m ->; apply: rpred_int. Qed.

Lemma Cint0 : 0 \is a Cint. Proof. exact: (Cint_int 0). Qed.
Lemma Cint1 : 1 \is a Cint. Proof. exact: (Cint_int 1). Qed.
Hint Resolve Cint0 Cint1.

Fact Cint_subring : subring_closed Cint.
Proof.
by split=> // _ _ /CintP[m ->] /CintP[p ->];
    rewrite -(rmorphB, rmorphM) Cint_int.
Qed.
Canonical Cint_opprPred := OpprPred Cint_subring.
Canonical Cint_addrPred := AddrPred Cint_subring.
Canonical Cint_mulrPred := MulrPred Cint_subring.
Canonical Cint_zmodPred := ZmodPred Cint_subring.
Canonical Cint_semiringPred := SemiringPred Cint_subring.
Canonical Cint_smulrPred := SmulrPred Cint_subring.
Canonical Cint_subringPred := SubringPred Cint_subring.

Lemma Creal_Cint : {subset Cint <= Num.real}.
Proof. by move=> _ /CintP[m ->]; apply: realz. Qed.

Lemma Cint_normK x : x \is a Cint -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/Creal_Cint/real_normK. Qed.

Lemma CintEsign x : x \is a Cint -> x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by move/Creal_Cint/realEsign. Qed.

(* Relating Cint and Cnat. *)

Lemma Cint_Cnat : {subset Cnat <= Cint}.
Proof. by move=> _ /CnatP[n ->]; rewrite pmulrn Cint_int. Qed.

Lemma CintE x : (x \is a Cint) = (x \is a Cnat) || (- x \is a Cnat).
Proof.
apply/idP/idP=> [/CintP[[n | n] ->] | ]; first by rewrite Cnat_nat.
  by rewrite NegzE opprK Cnat_nat orbT.
by case/pred2P=> [<- | /(canLR (@opprK _)) <-]; rewrite ?rpredN rpred_nat.
Qed.

Lemma Cnat_norm_Cint x : x \is a Cint -> `|x| \is a Cnat.
Proof.
case/CintP=> [m ->]; rewrite [m]intEsign rmorphM rmorph_sign.
by rewrite normrM normr_sign mul1r normr_nat rpred_nat.
Qed.

Lemma CnatEint x : (x \is a Cnat) = (x \is a Cint) && (0 <= x).
Proof.
apply/idP/andP=> [Nx | [Zx x_ge0]]; first by rewrite Cint_Cnat ?Cnat_ge0.
by rewrite -(ger0_norm x_ge0) Cnat_norm_Cint.
Qed.

Lemma CintEge0 x : 0 <= x -> (x \is a Cint) = (x \is a Cnat).
Proof. by rewrite CnatEint andbC => ->. Qed.

Lemma Cnat_exp_even x n : ~~ odd n -> x \is a Cint -> x ^+ n \is a Cnat.
Proof.
move=> n_oddF x_Cint; rewrite CnatEint; apply/andP; split.
  by apply: (rpredX _ x_Cint).
by apply: (real_exprn_even_ge0 (Creal_Cint x_Cint) n_oddF).
Qed.

Lemma norm_Cint_ge1 x : x \is a Cint -> x != 0 -> 1 <= `|x|.
Proof.
rewrite -normr_eq0 => /Cnat_norm_Cint/CnatP[n ->].
by rewrite pnatr_eq0 ler1n lt0n.
Qed.

Lemma sqr_Cint_ge1 x : x \is a Cint -> x != 0 -> 1 <= x ^+ 2.
Proof.
by move=> Zx nz_x; rewrite -Cint_normK // expr_ge1 ?normr_ge0 ?norm_Cint_ge1.
Qed.

Lemma Cint_ler_sqr x : x \is a Cint -> x <= x ^+ 2.
Proof.
move=> Zx; have [-> | nz_x] := eqVneq x 0; first by rewrite expr0n.
apply: ler_trans (_ : `|x| <= _); first by rewrite real_ler_norm ?Creal_Cint.
by rewrite -Cint_normK // ler_eexpr // norm_Cint_ge1.
Qed.

(* Relating Cnat and oldCnat. *)

Lemma truncC_old x : (truncC x = if (0 <= x) then `|floorC x|%N else 0%N).
Proof.
case: ifP => [x_ge0 | x_ge0F]; last by rewrite /truncC; apply: ifF.
have /andP [fl_ler lt_fl] : (`|floorC x|%N)%:R <= x < (`|floorC x|%N).+1%:R.
  have /andP[lemx ltxm1] := floorC_itv (ger0_real x_ge0).
  rewrite -addn1 !pmulrn PoszD gez0_abs ?lemx //.
  by rewrite -ltz_addr1 -(ltr_int R) (ler_lt_trans x_ge0).
have /andP [tr_ler lt_tr] := (truncC_itv x_ge0).
apply/eqP; rewrite eqn_leq; apply/andP.
do 2?[rewrite -ltnS -(ltr_nat R)]; split.
  by apply: (ler_lt_trans tr_ler lt_fl).
by apply: (ler_lt_trans fl_ler lt_tr).
Qed.

(* predCmod *)
Variables (U V : lmodType R) (f : {additive U -> V}).

Lemma raddfZ_Cint a u : a \is a Cint -> f (a *: u) = a *: f u. 
Proof. by case/CintP=> m ->; rewrite !scaler_int raddfMz. Qed.

Lemma rpredZ_Cint S (subS : @zmodPred V S) (kS : keyed_pred subS) :
  {in Cint & kS, forall z u, z *: u \in kS}.
Proof. by move=> _ u /CintP[m ->]; apply: rpredZint. Qed.

(* autC *)
Lemma aut_Cint nu : {in Cint, nu =1 id}.
Proof. by move=> _ /CintP[m ->]; apply: rmorph_int. Qed.

End CintTheory.

End ArchiNumDomainTheory.

Implicit Arguments Cnat [R].
Implicit Arguments Cint [R].
Implicit Arguments natCK [R].
Implicit Arguments truncC [R].
Hint Resolve truncC0 truncC1 Cnat_nat Cnat0 Cnat1.
Hint Resolve floorC0 floorC1 Cint_int Cint0 Cint1.

Section ArchiNumFieldTheory.

Variable R : archiNumFieldType.

Implicit Type nu : {rmorphism R -> R}.

Lemma Cnat_aut nu x : (nu x \is a Cnat) = (x \is a Cnat).
Proof.
by do [apply/idP/idP=> Nx; have:= aut_Cnat nu Nx] => [/fmorph_inj <- | ->].
Qed.

Lemma Cint_aut nu x : (nu x \is a Cint) = (x \is a Cint).
Proof. by rewrite !CintE -rmorphN !Cnat_aut. Qed.

End ArchiNumFieldTheory.

Section ArchiNumClosedFieldTheory.

Variable R : archiNumClosedFieldType.

Implicit Type x y : R.

Lemma conj_Cnat x : x \is a Cnat -> x^* = x.
Proof. by case/CnatP=> n ->; apply: rmorph_nat. Qed.

Lemma conj_Cint x : x \is a Cint -> x^* = x.
Proof. by move/Creal_Cint/conj_Creal. Qed.

End ArchiNumClosedFieldTheory.
End Theory.

Export Archi.ArchiNumDomain.Exports Archi.ArchiNumField.Exports.
Export Archi.ArchiNumClosedField.Exports Archi.ArchiRealDomain.Exports.
Export Archi.ArchiRealField.Exports Archi.ArchiRealClosedField.Exports.

Import Theory.

(* int is a archiRealDomain *)

Module intArchimedean.
Section intArchimedean.

Fact archimedean_axiomz : Num.archimedean_axiom int_numDomainType.
Proof. by move=> x; exists (absz x).+1; rewrite natz ltz_nat ltnSn. Qed.

End intArchimedean.
End intArchimedean.

Canonical int_archiNumDomain := 
  Eval hnf in ArchiNumDomainType int intArchimedean.archimedean_axiomz.
Canonical int_archiRealDomain :=
  Eval hnf in [archiRealDomainType of int].

Section ZnatPred.

Definition Znat := (@Cnat int_archiRealDomain).
Fact Znat_key : pred_key Znat. by []. Qed.
Canonical Znat_keyd := KeyedQualifier Znat_key.

Lemma ZnatP (m : int) : reflect (exists n : nat, m = n) (m \is a Znat).
Proof. 
by apply: (iffP (CnatP m)) => [[n ->] | [n ->]]; exists n; rewrite natz.
Qed.

Lemma Znat_semiring_closed : semiring_closed Znat.
Proof. exact: (Cnat_semiring int_archiRealDomain). Qed.
Canonical Znat_addrPred := AddrPred Znat_semiring_closed.
Canonical Znat_mulrPred := MulrPred Znat_semiring_closed.
Canonical Znat_semiringPred := SemiringPred Znat_semiring_closed.

Lemma Znat_def (m : int) : (m \is a Znat) = (0 <= m).
Proof. by case: m => [m | //]; rewrite le0z_nat; apply/ZnatP; exists m. Qed.

Lemma Znat_old (m : int) : (m \is a Znat) = (m \is a ssrint.Znat).
Proof. by apply/ZnatP/ssrint.ZnatP. Qed.

End ZnatPred.

Canonical rat_archiNumDomain := 
  Eval hnf in ArchiNumDomainType rat rat_archimedean.
Canonical rat_archiRealDomain :=
  Eval hnf in [archiRealDomainType of rat].
Canonical rat_archiNumField :=
  Eval hnf in [archiNumFieldType of rat].
Canonical rat_archiRealField :=
  Eval hnf in [archiRealFieldType of rat].


Section QintPred.

Definition Qint := (@Cint rat_archiRealField).
Fact Qint_key : pred_key Qint. by []. Qed.
Canonical Qint_keyed := KeyedQualifier Qint_key.

Lemma QintP (x : rat) : reflect (exists z : int, x = z%:~R) (x \is a Qint).
Proof. exact: CintP. Qed.

Fact Qint_subring_closed : subring_closed Qint.
Proof. exact: (Cint_subring rat_archiRealField). Qed.
Canonical Qint_opprPred := OpprPred Qint_subring_closed.
Canonical Qint_addrPred := AddrPred Qint_subring_closed.
Canonical Qint_mulrPred := MulrPred Qint_subring_closed.
Canonical Qint_zmodPred := ZmodPred Qint_subring_closed.
Canonical Qint_semiringPred := SemiringPred Qint_subring_closed.
Canonical Qint_smulrPred := SmulrPred Qint_subring_closed.
Canonical Qint_subringPred := SubringPred Qint_subring_closed.

Lemma Qint_def (x : rat) : (x \is a Qint) = (denq x == 1).
Proof.
apply/QintP/idP => [[y ->] | /eqP H]; first by rewrite denq_int.
by exists (numq x); rewrite numqE H mulr1.
Qed.

Lemma Qint_old (x : rat) : (x \is a Qint) = (x \is a rat.Qint).
Proof. by apply/QintP/rat.QintP. Qed.

Lemma numqK : {in Qint, cancel (fun x => numq x) intr}.
Proof. by move=> x; rewrite Qint_def numqE => /eqP ->; rewrite mulr1. Qed.

End QintPred.

Section QnatPred.

Definition Qnat := (@Cnat rat_archiRealField).
Fact Qnat_key : pred_key Qnat. by []. Qed.
Canonical Qnat_keyed := KeyedQualifier Qnat_key.

Lemma QnatP (x : rat) : reflect (exists n : nat, x = n%:R) (x \in Qnat).
Proof. exact: CnatP. Qed.

Lemma Qnat_def (x : rat) : (x \is a Qnat) = (x \is a Qint) && (0 <= x).
Proof. exact: CnatEint. Qed.

Lemma Qnat_old (x : rat) : (x \is a Qnat) = (x \is a rat.Qnat).
Proof. by apply/QnatP/rat.QnatP. Qed.

Fact Qnat_semiring_closed : semiring_closed Qnat.
Proof. exact: (Cnat_semiring rat_archiRealField). Qed.
Canonical Qnat_addrPred := AddrPred Qnat_semiring_closed.
Canonical Qnat_mulrPred := MulrPred Qnat_semiring_closed.
Canonical Qnat_semiringPred := SemiringPred Qnat_semiring_closed.

End QnatPred.

(* TODO
Lemma Qint_dvdz (m d : int) : (d %| m)%Z -> ((m%:~R / d%:~R : rat) \is a Qint).

Lemma Qnat_dvd (m d : nat) : (d %| m)%N → ((m%:R / d%:R : rat) \is a Qnat).

+ locate other occurences
*)

Module algCArchimedean.
Section algCArchimedean.

Fact algC_archiAxiom : Num.archimedean_axiom algCnumClosedField.
Proof. 
exact: (algebraics_fundamentals.rat_algebraic_archimedean algC_algebraic). 
Qed.

End algCArchimedean.
End algCArchimedean.

Canonical algCarchiNumDomain := 
  ArchiNumDomainType algC algCArchimedean.algC_archiAxiom.
Canonical algCarchiNumFieldType := [archiNumFieldType of algC].
Canonical algCarchiNumClosedFieldType := [archiNumClosedFieldType of algC].

Section algCPred.

Lemma Cint_old (x : algC) : (x \is a Cint) = (x \in Algebraics.Exports.Cint).
Proof. by apply/CintP/algC.CintP. Qed.

Lemma Cnat_old (x : algC) : (x \is a Cnat) = (x \in Algebraics.Exports.Cnat).
Proof. by apply/CnatP/algC.CnatP. Qed.

End algCPred.

Section NCFComplements.

Variable R : numClosedFieldType.
Implicit Types x y : R.

(* complete order not compatible with all operations ! *)

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
  by rewrite (gtr_eqF Rxy).
move=> /orP[ | /andP[/eqP Ryx Iyx]].
+ by rewrite Rxy ltrr.
rewrite [x]Crect [y]Crect Rxy.
by move: Iyx; rewrite ler_eqVlt (ler_gtF Ixy) orbF => /eqP ->.
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
rewrite /lttc /letc negb_or negb_and.
case: (boolP (x == y)) => [/eqP -> | ]; first by rewrite eq_refl lerr /= !andbF.
move=> x_neqy; rewrite /= andbT.
rewrite -?real_ltrNge -?real_lerNgt ?Creal_Re ?Creal_Im ?ler_eqVlt //.
have x_rect := (Crect x); have y_rect := (Crect y).
have [ | | eq_Re] //= := (real_ltrgtP (Creal_Re x) (Creal_Re y)).
have [ | | eq_Im] //= := (real_ltrgtP (Creal_Im x) (Creal_Im y)).
by move: x_neqy; rewrite x_rect y_rect eq_Re eq_Im eq_refl.
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

Lemma neq_lttc x y :
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

Lemma letcW_mono_Cto (R' : eqType) (f : R -> R') (g : rel R') :
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

Lemma letc_sum (I : Type) (r : seq I) (P : pred I) (F G : I -> R) :
  (forall i : I, P i -> letc (F i) (G i)) -> 
  letc (\sum_(i <- r | P i) F i) (\sum_(i <- r | P i) G i).
Proof. by exact: (big_ind2 _ (letcc _) letc_add). Qed.

(* changer l'énoncé pour la size *)
Lemma lttc_sum (I : Type) (r : seq I) (F G : I -> R) :
  (0 < size r)%N -> (forall i : I, lttc (F i) (G i)) -> 
  lttc (\sum_(i <- r) F i) (\sum_(i <- r) G i).
Proof.
case: r => [// | x r _ Hi]; rewrite big_cons big_cons.
apply: (@lttc_le_trans (G x + \sum_(j <- r) F j)); first by rewrite lttc_add2r.
by rewrite letc_add2l; apply: letc_sum => i _; rewrite letc_eqVlt Hi orbT.
Qed.

(* letc_iff *)
Definition letcif x y (C : bool) : Prop :=
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

Lemma mono_letcif (f : R -> R) C :
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

Lemma letcif_sum (I : finType) (P C : pred I) (E1 E2 : I -> R) :
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



(*       sequence of the roots of a polynomial     *)
Definition sroots (P : {poly R}) := if P == 0 then [::] 
                                      else(sval(closed_field_poly_normal P)).

Lemma sroots_0 : sroots 0 = [::].
Proof. by rewrite /sroots eq_refl. Qed.


Lemma sroots_poly P : P = lead_coef P *: \prod_(x <- (sroots P)) ('X - x%:P). 
Proof.
case: (boolP (P == 0)) => [/eqP -> | /negbTE P_neq0].
  by rewrite lead_coef0 scale0r.
by rewrite /sroots P_neq0 {1}(svalP(closed_field_poly_normal P)).
Qed.

Lemma srootsP P x : P != 0 -> reflect (x \in sroots P) (root P x).
Proof.
move=> P_neq0.
have lead_coef_neq0 : lead_coef P != 0; first by rewrite lead_coef_eq0.
move: P_neq0 (svalP(closed_field_poly_normal P)) => /negbTE P_neq0 H; rewrite H.
rewrite (rootZ _ _ lead_coef_neq0) -H root_prod_XsubC /sroots P_neq0.
by apply: (iffP idP).
Qed.

Lemma sroots_neq0 P : (P != 0) -> (0 \in (sroots P)) = (P`_0 == 0).
Proof.
move=> P_neq0; apply/idP/idP.
  by move/(srootsP _ P_neq0)/rootP; rewrite horner_coef0 => ->.
by move=> /eqP H; apply/(srootsP _ P_neq0)/rootP; rewrite horner_coef0.
Qed.

Lemma sroots_mu P x : (count_mem x) (sroots P) = \mu_x P.
Proof.
case: (boolP (P == 0)) =>  [/eqP P_eq0 | P_neq0].
  by rewrite P_eq0 sroots_0 mu0; apply/count_memPn; rewrite in_nil.
case: (boolP (root P x)) => [x_root | x_not_root]; last first.
  rewrite (muNroot x_not_root); apply/count_memPn.
  by apply/negP; apply: (elimN (srootsP x P_neq0) x_not_root).
have [sr_eq] : sroots P = sval(closed_field_poly_normal P).
  by rewrite /sroots; move/negbTE: P_neq0 => P_neq0; rewrite ifF.
move: (svalP (closed_field_poly_normal P)); rewrite -sr_eq.
rewrite -prodr_undup_exp_count.
have x_seqroot : x \in undup (sroots P); first by rewrite mem_undup; apply /srootsP.
rewrite (bigD1_seq _ x_seqroot (undup_uniq (sroots P))) /= scalerAr mulrC => P_eq.
apply/eqP; rewrite -(muP _ _ P_neq0); apply/andP; split.
  by apply/dvdpP; exists (lead_coef P *: 
    \prod_(i <- undup (sroots P) | i != x) ('X - i%:P) ^+ (count_mem i) (sroots P)).
rewrite [X in _ %| X]P_eq exprS dvdp_mul2r; last first.
  by rewrite expf_neq0 // polyXsubC_eq0.
rewrite dvdp_XsubCl; move: P_neq0; rewrite -lead_coef_eq0 => lc_P_neq0.
rewrite (rootZ _ _ lc_P_neq0) prodr_undup_exp_count.
by rewrite -big_filter root_prod_XsubC mem_filter eq_refl.
Qed.

Lemma sroots_size P : size (sroots P) = if (P == 0) then 0%N else (size P).-1.
Proof.
case: (boolP (P == 0)) => [/eqP ->| H].
  by rewrite sroots_0.
have Hp : (0 < size P)%N; first by rewrite size_poly_gt0.
rewrite /sroots; move/negbTE : H => H; rewrite H; move/negbT: H => H.
move: (svalP( closed_field_poly_normal P)); set r := sval _ => ->.
move: H; rewrite -lead_coef_eq0 => H; rewrite (size_scale _ H).
by rewrite size_prod_XsubC.
Qed.

Lemma sroots_polyC c : sroots c%:P = [::].
Proof.
apply: size0nil; rewrite sroots_size.
case: (boolP (c == 0)) => [/eqP -> | /negbTE c_neq0] /=.
  by rewrite eq_refl.
by rewrite polyC_eq0 c_neq0 size_polyC; move/negbT: c_neq0 => -> /=.
Qed.

Lemma srootsM P Q : P * Q != 0 ->
  perm_eq (sroots (P * Q)) ((sroots P) ++ (sroots Q)).
Proof.
move => PQ_neq0; rewrite /perm_eq; apply/allP => x.
rewrite !mem_cat => /orP [ H | /orP [H | H]] /=; 
by rewrite count_cat !sroots_mu (mu_mul _ PQ_neq0).
Qed.

Lemma srootsZ P a : a != 0 -> 
  perm_eq (sroots (a *: P)) (sroots P).
Proof.
case: (boolP (P == 0)) => [/eqP -> //= _ | P_neq0 a_neq0].
  by rewrite scaler0.
rewrite -mul_polyC.
apply/(perm_eq_trans (srootsM _ )).
  by apply/mulf_neq0 => //; rewrite polyC_eq0.
by rewrite sroots_polyC.
Qed.

Lemma sroots_prod (I : Type) P (r : seq I) : all [pred i | P i != 0] r ->
  perm_eq (sroots (\prod_(i <- r) P i)) (flatten [seq sroots (P i) | i <- r]).
Proof.
elim: r => [_ | j r Ihr].
  rewrite big_nil /=; have -> : (sroots 1) = [::]; last by [].
  have -> : (1 = (1%:P : poly_ringType R)); first by [].
  by rewrite sroots_polyC.
rewrite /= => /andP [Hj Hprod].
rewrite big_cons; apply: (perm_eq_trans (srootsM _)).
  apply:mulf_neq0; first by [].
  by rewrite prodf_seq_neq0.
by rewrite perm_cat2l; apply: Ihr.
Qed.

Lemma sroots_XsubC a : sroots ('X - a%:P) = [:: a].
Proof.
set s := sroots _.
have size_s : size s = 1%N.
  by rewrite sroots_size polyXsubC_eq0 size_XsubC.
have := (root_XsubC a a); rewrite eq_refl.
have : 'X - a%:P != 0 by rewrite polyXsubC_eq0.
move/(srootsP _) => H; move/H; rewrite -/s.
have -> : s = (head 0 s) :: (behead s).
  apply: (@eq_from_nth _ 0) => /=.
    by rewrite size_behead size_s.
  by move=> i; rewrite size_s ltnS leqn0 => /eqP ->; rewrite [RHS]/= nth0.
have -> : behead s = [::].
  by apply/eqP; rewrite -size_eq0 size_behead size_s.
by rewrite inE => /eqP ->.
Qed.

Lemma sroots_prod_XsubC rs :
  perm_eq (sroots (\prod_(x <- rs) ('X - x%:P))) rs.
Proof.
apply/(perm_eq_trans (sroots_prod _) _).
  by apply/allP=> x _ /=; rewrite polyXsubC_eq0.
rewrite (eq_map sroots_XsubC).
by elim: rs => //= x rs H /=; rewrite perm_cons.
Qed.

Lemma sroots_separable P :
  separable.separable_poly P -> uniq (sroots P).
Proof.
case: (boolP (P == 0)) => [/eqP -> _ | P_neq0].
  by rewrite /sroots eq_refl.
rewrite [X in separable.separable_poly X]sroots_poly /separable.separable_poly.
rewrite derivZ coprimep_scalel ?coprimep_scaler ?lead_coef_eq0 //.
by rewrite -separable.separable_prod_XsubC.
Qed.

Lemma sroots_eqp P Q :
  P %= Q -> perm_eq (sroots P) (sroots Q).
Proof.
case: (boolP  (P == 0)) => [/eqP -> | P_neq0 P_eqp_Q].
  by rewrite eqp_sym eqp0 => /eqP ->.
have Q_neq0 : Q != 0.
  apply/negP => /eqP H; rewrite H eqp0 in P_eqp_Q.
  by move: P_eqp_Q; apply/negP.
move/eqpf_eq : P_eqp_Q => [l /= l_neq0 ->].
by apply: srootsZ.
Qed.

End NCFComplements.

Arguments letc [R].

Section Algr.

Variable T : numClosedFieldType.

Local Notation aCnum := Algebraics.Implementation.numClosedFieldType.

Lemma minCpolyP_irr (x : algC) : irreducible_poly (sval (minCpolyP x)).
Proof.
have [[P_eq P_mon] P_div] := svalP (minCpolyP x).
rewrite /irreducible_poly; apply: pair.
  have /negP/negP/root_size_gt1 := (minCpoly_eq0 x).
  by move/(_ _ (root_minCpoly x)); rewrite [in X in size X]P_eq size_map_poly.
move=> Q /negbTE size_Q Q_div; rewrite /eqp Q_div andTb -P_div.
have /dvdpP[R R_eq] := Q_div.
have := (root_minCpoly x); rewrite P_eq R_eq rmorphM /= rootM !P_div R_eq.
move/orP => [| //]; rewrite -[X in (_ %| X)]mulr1 dvdp_mul2l ?dvdp1 ?size_Q //.
by move/monic_neq0: P_mon; rewrite R_eq; apply: contraNneq => ->; rewrite mul0r.
Qed.

Lemma minCpoly_root_irr (x y : algC) : 
  root (minCpoly x) y -> minCpoly x = minCpoly y.
Proof.
move=> y_root; apply/eqP; rewrite -eqp_monic ?minCpoly_monic //.
have [[P_eq P_mon] P_div] := svalP (minCpolyP x).
have [[Q_eq Q_mon] Q_div] := svalP (minCpolyP y).
have := y_root; rewrite P_eq Q_eq Q_div => H.
have := (snd (minCpolyP_irr x)) (sval (minCpolyP y)).
have /negP/negP/root_size_gt1 := (minCpoly_eq0 y).
move/(_ _ (root_minCpoly y)); rewrite [in X in size X]Q_eq size_map_poly.
rewrite ltn_neqAle eq_sym => /andP[H1 _].
by move/(_ H1 H) => {H1 H}; rewrite eqp_map eqp_sym.
Qed.

Lemma minCpoly_separable (x : algC) :
  separable.separable_poly (minCpoly x).
Proof.
apply/Pdiv.ClosedField.root_coprimep => y /minCpoly_root_irr ->; rewrite -rootE.
have [[Q_eq Q_mon] Q_div] := svalP (minCpolyP y); rewrite Q_eq deriv_map Q_div.
rewrite gtNdvdp ?lt_size_deriv //; last by rewrite monic_neq0.
have /negP/negP/root_size_gt1 := (minCpoly_eq0 y); move/(_ _ (root_minCpoly _)).
rewrite [in X in size X]Q_eq size_map_poly -[1%N]add1n -ltn_subRL subn1.
by rewrite -size_deriv lt0n size_poly_eq0.
Qed.

Lemma minCpoly_coprime (x y : algC) :
  ~~ root (minCpoly x) y -> coprimep (minCpoly x) (minCpoly y).
Proof.
move=> /negP y_nroot; apply/Pdiv.ClosedField.coprimepP => z.
move /minCpoly_root_irr => eq_xz; rewrite -rootE.
apply/negP => /minCpoly_root_irr; rewrite -eq_xz.
by move=> eq_yx; apply: y_nroot; rewrite -eq_yx root_minCpoly.
Qed.

Locate countFieldType.

Lemma minCpoly_field_extension (F : countFieldType) (x : algC) 
      (FtoC : {rmorphism F -> algC}) (FtoT : {rmorphism F -> T}) :
  {E : countFieldType & 
       {FtoE : {rmorphism F -> E} &
{EtoC : {rmorphism E -> algC} | EtoC \o FtoE =1 FtoC} &
{EtoT : {rmorphism E -> T} | EtoT \o FtoE =1 FtoT} &

{u : E | x = EtoC u} & {v : E | x^* = EtoC (v)} &
{




       {w : E | root (map_poly ratr (sval (minCpolyP x))) w
                & forall u : E, exists q, u = (map_poly FtoE q).[w]}}}}}.

Locate countType.
Search _ "count" in choice.
About fin_all_exists.

Search _ "morph" in ssrnum.

Section FieldExtComplements.

Local Open Scope quotient_scope.

Variables (x y : algC).


       (*       |-----------------rat-----------------|       *)
       (*       |               /     \               |       *)
       (*    f0 |     g0       v  Qx   v       g1     | f1    *)
       (*       |   ---------Q(z0)<->Q(z0)---------   |       *)
       (*       |  /                               \  |       *)
       (*       v /       h0                h1      \ v       *)
       (*       aC <---------- Q(z0)(z1) -----------> T       *)

Definition f0 := (@ratr_rmorphism aCnum).
Definition f1 := (@ratr_rmorphism T).

Definition px := sval (minCpolyP x).

Lemma px_aC : root (map_poly f0 px) x.
Proof. by have [[_ _] ->] := svalP (minCpolyP x); apply: dvdpp. Qed.

Lemma px_cT : root (map_poly f1 px) (algr x).
Proof. by apply: algr_root. Qed.

Let irr_px : irreducible_poly px.
Proof. by apply: minCpolyP_irr. Qed.

(* Q(z0) *)
Definition Qx_aC := SubFieldExtType px_aC irr_px. 
Definition Qx_cT := SubFieldExtType px_cT irr_px.

(* canonical structures *)
Canonical Qx_aC_eqType := [eqType of Qx_aC].
Canonical Qx_aC_choiceType := [choiceType of Qx_aC].
Canonical Qx_aC_quotType := [quotType of Qx_aC].
Canonical Qx_aC_eqQuotType := 
  [eqQuotType (@equiv_subfext _ _ f0 x px) of Qx_aC].
Canonical Qx_aC_zmodType := [zmodType of Qx_aC].
Canonical Qx_aC_ringType := [ringType of Qx_aC].
Canonical Qx_aC_comRingType := [comRingType of Qx_aC].
Canonical Qx_aC_unitRingType := [unitRingType of Qx_aC].
Canonical Qx_aC_comUnitRingType := [comUnitRingType of Qx_aC].
Canonical Qx_aC_idomainType := [idomainType of Qx_aC].
Canonical Qx_aC_fieldType := [fieldType of Qx_aC].
Canonical Qx_aC_lmodType := [lmodType rat of Qx_aC].
Canonical Qx_aC_lalgType := [lalgType rat of Qx_aC].
Canonical Qx_aC_algType := [algType rat of Qx_aC].
Canonical Qx_aC_unitAlgType := [unitAlgType rat of Qx_aC].
Canonical Qx_aC_vectType2 := [vectType rat of Qx_aC].
Canonical Qx_aC_falgType := [FalgType rat of Qx_aC].
Canonical Qx_aC_fieldExtType := [fieldExtType rat of Qx_aC].

Canonical Qx_cT_eqType := [eqType of Qx_cT].
Canonical Qx_cT_choiceType := [choiceType of Qx_cT].
Canonical Qx_cT_quotType := [quotType of Qx_cT].
Canonical Qx_cT_eqQuotType := 
  [eqQuotType (@equiv_subfext _ _ f1 (algr x) px) of Qx_cT].
Canonical Qx_cT_zmodType := [zmodType of Qx_cT].
Canonical Qx_cT_ringType := [ringType of Qx_cT].
Canonical Qx_cT_comRingType := [comRingType of Qx_cT].
Canonical Qx_cT_unitRingType := [unitRingType of Qx_cT].
Canonical Qx_cT_comUnitRingType := [comUnitRingType of Qx_cT].
Canonical Qx_cT_idomainType := [idomainType of Qx_cT].
Canonical Qx_cT_fieldType := [fieldType of Qx_cT].
Canonical Qx_cT_lmodType := [lmodType rat of Qx_cT].
Canonical Qx_cT_lalgType := [lalgType rat of Qx_cT].
Canonical Qx_cT_algType := [algType rat of Qx_cT].
Canonical Qx_cT_unitAlgType := [unitAlgType rat of Qx_cT].
Canonical Qx_cT_vectType2 := [vectType rat of Qx_cT].
Canonical Qx_cT_falgType := [FalgType rat of Qx_cT].
Canonical Qx_cT_fieldExtType := [fieldExtType rat of Qx_cT].


Definition g0 := (subfx_inj_rmorphism f0 x px).
Definition g1 := (subfx_inj_rmorphism f1 (algr x) px).

(* Definition d :=  (size px).-1. *)

(* Lemma cast_Qx_aC : (size (if (px != 0) && root (map_poly f0 px) x  *)
(*                       then (lead_coef px)^-1 *: px else 'X)).-1 = d. *)
(* Proof. *)
(* have H := (irredp_neq0 irr_px). *)
(* by rewrite /d px_aC H /= size_scale // invr_eq0 lead_coef_eq0 H. *)
(* Qed. *)

(* Lemma cast_Qx : (size (if (px != 0) && root (map_poly f0 px) x  *)
(*                       then (lead_coef px)^-1 *: px else 'X)).-1 = *)
(*                 (size (if (px != 0) && root (map_poly f1 px) (algr x)  *)
(*                       then (lead_coef px)^-1 *: px else 'X)).-1. *)
(* Proof. by rewrite px_cT px_aC. Qed. *)

Definition Qx_aCtocT (z : Qx_aC) : Qx_cT := 
  (subfx_eval f1 (algr x) px) (sval (sig_eqW (subfxE z)) %% px).

Definition Qx_cTtoaC (z : Qx_cT) : Qx_aC :=
  (subfx_eval f0 x px) (sval (sig_eqW (subfxE z)) %% px).

Lemma Qx_aCtocTK : cancel Qx_aCtocT Qx_cTtoaC.
Proof.
move/subfx_irreducibleP: irr_px =>/=/(_ _ _ _ px_cT (irredp_neq0 irr_px)) min_p.
move=> z; rewrite /Qx_aCtocT /Qx_cTtoaC; case: (sig_eqW  _) => /= q ->.
have FLinj_aC : injective (@subfx_inj _ _ f0 x px). 
  by apply: fmorph_inj.
apply: FLinj_aC; rewrite !(subfx_inj_eval px_aC (irredp_neq0 irr_px)).
rewrite [in RHS](divp_eq q px) rmorphD rmorphM /= !hornerE (eqP px_aC) mulr0.
rewrite add0r; case: (sig_eqW _) => /= r /(congr1 subfx_inj)/esym.
rewrite !(subfx_inj_eval px_cT (irredp_neq0 irr_px)) {1}(divp_eq r px).
rewrite rmorphD rmorphM /= !hornerE (eqP px_cT) mulr0 add0r => /eqP H.
apply/eqP; move: H; rewrite -![_ == _.[_]]subr_eq0 -!hornerN -!hornerD.
rewrite -!rmorphB /= -modp_opp -modp_add => /eqP/rootP/min_p H.
case: (boolP ((r - q) %% px == 0)) => [/eqP -> | /H {H}].
  by rewrite rmorph0 horner0.
by rewrite leqNgt ltn_modp (irredp_neq0 irr_px).
Qed.

Lemma Qx_cTtoaCK : cancel Qx_cTtoaC Qx_aCtocT.
Proof.
move/subfx_irreducibleP: irr_px =>/=/(_ _ _ _ px_aC (irredp_neq0 irr_px)) min_p.
move=> z; rewrite /Qx_aCtocT /Qx_cTtoaC; case: (sig_eqW  _) => /= q ->.
have FLinj_cT : injective (@subfx_inj _ _ f1 (algr x) px). 
  by apply: fmorph_inj.
apply: FLinj_cT; rewrite !(subfx_inj_eval px_cT (irredp_neq0 irr_px)).
rewrite [in RHS](divp_eq q px) rmorphD rmorphM /= !hornerE (eqP px_cT) mulr0.
rewrite add0r; case: (sig_eqW _) => /= r /(congr1 subfx_inj)/esym.
rewrite !(subfx_inj_eval px_aC (irredp_neq0 irr_px)) {1}(divp_eq r px).
rewrite rmorphD rmorphM /= !hornerE (eqP px_aC) mulr0 add0r => /eqP H.
apply/eqP; move: H; rewrite -![_ == _.[_]]subr_eq0 -!hornerN -!hornerD.
rewrite -!rmorphB /= -modp_opp -modp_add.
by move => /eqP/rootP/algr_root_map/rootP ->.
Qed.

Lemma Qx_aCtocT_is_rmorphism : rmorphism Qx_aCtocT.
Proof.
have FLinj_cT : injective (@subfx_inj _ _ f1 (algr x) px) by apply: fmorph_inj.
split; [move=> a b | split; [move => a b | ]]; rewrite /Qx_aCtocT; last first.
+ apply/FLinj_cT/eqP; rewrite !(subfx_inj_eval px_cT (irredp_neq0 irr_px)).
  case: (sig_eqW _) => /= q /(congr1 subfx_inj)/esym/eqP.
  rewrite (subfx_inj_eval px_aC (irredp_neq0 irr_px)) !rmorph1.
  rewrite {1}(divp_eq q px) rmorphD rmorphM /= !hornerE (eqP px_aC) mulr0 add0r.
  have -> : 1 = (map_poly f1 (1%:P %% px)).[algr x].
    rewrite modp_small; last by rewrite size_polyC oner_neq0 irr_px.1.
    by rewrite !rmorph1 hornerC.
  have -> : 1 = (map_poly f0 (1%:P %% px)).[x].
    rewrite modp_small; last by rewrite size_polyC oner_neq0 irr_px.1.
    by rewrite !rmorph1 hornerC.
  rewrite -![_ == _.[_]]subr_eq0 -!hornerN -!hornerD -!rmorphB /=.
  by rewrite -modp_opp -modp_add => /eqP/rootP/algr_root_map/rootP ->.
+ apply/FLinj_cT/eqP; rewrite rmorphM /=.
  rewrite !(subfx_inj_eval px_cT (irredp_neq0 irr_px)) -(@hornerM T).
  rewrite -rmorphM /= -subr_eq0 -hornerN -hornerD -rmorphB /=.
  apply/eqP; case: (sig_eqW _) => /= qab /esym/eqP.
  case: (sig_eqW _) => /= qa ->; case: (sig_eqW _) => /= qb ->.
  rewrite -(rmorphM _ qa qb) -subr_eq0 /= -rmorphB /= => /eqP/(congr1 subfx_inj).
  rewrite rmorph0 (subfx_inj_eval px_aC (irredp_neq0 irr_px)).
  rewrite {1}(divp_eq (qab - (qa * qb)) px) rmorphD rmorphM /= !hornerE.
  rewrite (eqP px_aC) mulr0 add0r => /rootP/algr_root_map/rootP H.
  rewrite (divp_eq (qab %% px - qa %% px * (qb %% px)) px) rmorphD rmorphM /=.
  rewrite !hornerE (eqP px_cT) mulr0 add0r.
  have <- //: (qab - qa * qb) %% px = (qab %% px - qa %% px * (qb %% px)) %% px.
  by rewrite !modp_add !modp_opp -modp_mul mulrC -modp_mul mulrC modp_mod.
apply/FLinj_cT/eqP; rewrite rmorphB /=.
rewrite !(subfx_inj_eval px_cT (irredp_neq0 irr_px)).
rewrite -hornerN -hornerD -rmorphB /= -subr_eq0 -hornerN -hornerD -rmorphB /=.
apply/eqP/rootP; rewrite -modp_opp -modp_add -modp_opp -modp_add.
case: (sig_eqW _) => /= qab /esym/eqP.
case: (sig_eqW _) => /= qa ->; case: (sig_eqW _) => /= qb ->.
rewrite -(rmorphB _ qa qb) -subr_eq0 -rmorphB /= => /eqP/(congr1 subfx_inj).
rewrite rmorph0 (subfx_inj_eval px_aC (irredp_neq0 irr_px)).
rewrite {1}(divp_eq (qab - (qa - qb)) px) rmorphD rmorphM /= !hornerE.
by rewrite (eqP px_aC) mulr0 add0r => /rootP/algr_root_map ->.
Qed.

Canonical Qx_aCtocT_additive := Additive Qx_aCtocT_is_rmorphism.
Canonical Qx_aCtocT_rmorphism := RMorphism Qx_aCtocT_is_rmorphism.

Lemma Qx_cTtoaC_is_rmorphism : rmorphism Qx_cTtoaC.
Proof. exact: (can2_rmorphism Qx_aCtocTK Qx_cTtoaCK). Qed.

Canonical Qx_cTtoaC_additive := Additive Qx_cTtoaC_is_rmorphism.
Canonical Qx_cTtoaC_rmorphism := RMorphism Qx_cTtoaC_is_rmorphism.

(* Lemma Qx_aCtocT_x : *)
(*   Qx_aCtocT (subfx_root f0 x px) = (subfx_root f1 (algr x) px). *)
(* Proof. *)

(* Search subfx_inj. *)


(* Lemma Qx_le (z1 z2 : Qx_aC) : *)
(*   letc (g0 z1) (g0 z2) = letc (g1 (Qx_aCtocT z1)) (g1 (Qx_aCtocT z2)). *)
(* Proof. *)
(* rewrite /g0. *)

(* Search _ subfx_inj. *)

(* Lemma Qx_algr_x : *)
(*   algr (g0 (subfx_root f0 x px)) = g1 (Qx_aCtocT (subfx_root f1 (algr x) px)). *)

Lemma Qx_algr (z : Qx_aC) :
  algr (g0 z) = g1 (Qx_aCtocT z).
Proof.
pose p := sval (minCpolyP (g0 z)).
have [[p_eq p_mon] p_div] := svalP (minCpolyP (g0 z)).
pose toQx_aC : rat -> Qx_aC := (inj_subfx_rmorphism f0 x px).
have z_root_aC : root (map_poly toQx_aC p) z.
  apply/rootP; rewrite /toQx_aC /=.
  have g0_aC : injective g0 by apply: fmorph_inj.
  apply : g0_aC; rewrite -horner_map -map_poly_comp /= rmorph0 -[_ z]/(g0 z).
  have H : (subfx_inj \o inj_subfx f0 x px) =1 ratr by apply: fmorph_eq_rat.
  rewrite (eq_map_poly H).
  by apply/rootP; rewrite p_div dvdpp.
have z_root : root (map_poly f1 p) (g1 (Qx_aCtocT z)).
  apply/rootP.
  have H : f1 =1 g1 \o Qx_aCtocT \o toQx_aC.
    move=> a; rewrite /toQx_aC.
    pose h := GRing.comp_rmorphism g1 (GRing.comp_rmorphism 
                           (Qx_aCtocT_rmorphism) (inj_subfx_rmorphism f0 x px)).
    by rewrite -[RHS]/(h a) [RHS]fmorph_eq_rat.
  rewrite (eq_map_poly H) map_poly_comp map_poly_comp horner_map horner_map.
  by have /rootP -> := z_root_aC; rewrite !rmorph0.
apply: (algr_def z_root).
About sroots.
About subfxEroot.
Search _ algr.
Search _ "poly" "ind".
Search _ dvdp map_poly.
Search _ "rat" (_ == 0).

  rewrite (eq_map_poly f0).


fmorph_eq_rat: forall (rR : unitRingType) (f : {rmorphism rat -> rR}), f =1 ratr
Search _ "eq" map_poly.
horner_map:
  forall (aR rR : ringType) (f : {rmorphism aR -> rR}) (p : {poly aR}) (x : aR),
  (map_poly f p).[f x] = f p.[x]
move/(map_poly_inj (@subfx_inj_rmorphism _ _ f0 x px)).

Search _ map_poly injective.
Search _ .
Locate "^:P".

map_poly_inj: forall (F : fieldType) (R : ringType) (f : {rmorphism F -> R}), injective (map_poly f)

Definition f_quot0 d := (fun x : 'rV[rat]_d => 
             (horner_morph (fun q : rat => mulrC (algr z0) (f1 q)) (rVpoly x))).
Definition g1 : Qz0 -> T := @lift_fun1 Qz0 (@f_quot0 _).

Fact pi_g1 : {mono \pi : x / (@f_quot0 _ x) >-> g1 x}.
Proof.
move=> x; apply/eqP; rewrite /g1 /f_quot0 /=; unlock.
rewrite /= -subr_eq0 -rmorphB.
About min_subfx_vectAxiom.
Print vector.Vector.axiom_def.
Print equiv_subfext.
Check (equiv_subfext _ x).
Search _ (lift_fun1 _ _).
About lift_fun1.

Fact pi_subfx_inj : {mono \pi : x / iotaFz x >-> subfx_inj x}.
Proof.
unlock subfx_inj => x; apply/eqP; rewrite -/(equiv_subfext _ x).
by rewrite -eqmodE reprK.
Qed.
Canonical pi_subfx_inj_morph := PiMono1 pi_subfx_inj.


(* rat -> Q(z0) *)
Definition iota0 := (inj_subfx f0 z0 p0).

Definition p1 := sval (minCpolyP z1).

(* Q(z0)(z1) *)
Definition Qz1 := subFExtend iotaC1 z1 (map_poly iota01 p1).






End FieldExtComplements.

End Algr.

Module complexArchimedean.
Section complexArchimedean.

Variable R : archiRcfType.

Lemma complex_archimedean : Num.archimedean_axiom (complex_numFieldType R).
Proof.
move => z.
have R_archi : Num.archimedean_axiom R; first by case:R => ? [].
have [n] := (R_archi (ComplexField.normc z)).
move/(ler_lt_trans (ler_norm _)); rewrite -ltcR rmorphMn => lt_n.
by exists n; apply/(ltr_le_trans lt_n).
Qed.

End complexArchimedean.
End complexArchimedean.

Canonical complex_archiNumDomain (R : archiRcfType) :=
  ArchiNumDomainType R[i] (@complexArchimedean.complex_archimedean R).
Canonical complex_archiNumField (R : archiRcfType) :=
  [archiNumFieldType of R[i]].
Canonical complex_archiNumClosedField (R : archiRcfType) :=
  [archiNumClosedFieldType of R[i]].

(* TODO realalg
Canonical complexalg_archiNumDomainType := [archiNumDomainType of complexalg].
Canonical complexalg_archiNumFieldType := [archiNumFieldType of complexalg].
Canonical complexalg_archiNumClosedFieldType := [archiNumClosedFieldType of complexalg].
*)

