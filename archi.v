From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import poly ssrint rat.
From mathcomp Require Import generic_quotient polyrcf interval.
From mathcomp Require Import realalg algC polyorder polydiv complex.
(* From mathcomp Require Import complex mxpoly fieldext polyorder polydiv algC. *)
(* From mathcomp Require Import matrix vector falgebra countalg. *)


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
Definition base4 R (c : class_of R) := 
  let: Class b m := c in @Num.ArchimedeanField.Class R b m.
Local Coercion base4 : class_of >-> Num.ArchimedeanField.class_of.

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
Definition archiFieldType := @Num.ArchimedeanField.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.RealField.class_of.
Coercion base2 : class_of >-> ArchiNumField.class_of.
Coercion base3 : class_of >-> ArchiRealDomain.class_of.
Coercion base4 : class_of >-> Num.ArchimedeanField.class_of.
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
Coercion archiFieldType : type >-> Num.ArchimedeanField.type.
Canonical archiFieldType.
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

Check x.
Check (0 <= x).

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

Module realalgArchimedean.
Section realalgArchimedean.

Fact realalg_archimedean : Num.archimedean_axiom realalg_numDomainType.
Proof. by move=> x; have := (@RealAlg.alg_archi archiType x). Qed.

End realalgArchimedean.
End realalgArchimedean.

Canonical realalg_archiNumDomainType :=
  ArchiNumDomainType realalg realalgArchimedean.realalg_archimedean.
Canonical realalg_archiNumFieldType := [archiNumFieldType of realalg].
Canonical realalg_archiRealDomainType := [archiRealDomainType of realalg].
Canonical realalg_archiRealFieldType := [archiRealFieldType of realalg].
Canonical realalg_archiRcfType := [archiRcfType of realalg].

Canonical complexalg_archiNumDomainType := [archiNumDomainType of complexalg].
Canonical complexalg_archiNumFieldType := [archiNumFieldType of complexalg].
Canonical complexalg_archiNumClosedFieldType := [archiNumClosedFieldType of complexalg].



Section NormRcfType.

(* Separate in numDomain, numField *)
Variable T : numClosedFieldType.

Structure normT := NormT {nval :> T ; _ : nval \is Num.real}.

Definition normT_of of (phant T) := normT.
Identity Coercion type_normT_of : normT_of >-> normT.

Local Notation "{ 'normT' T }" := (normT_of (Phant T)).

Canonical normT_subType := Eval hnf in [subType for nval].
Definition normT_eqMixin := Eval hnf in [eqMixin of normT by <:].
Canonical normT_eqType := Eval hnf in EqType normT normT_eqMixin.
Definition normT_choiceMixin := Eval hnf in [choiceMixin of normT by <:].
Canonical normT_choiceType := Eval hnf in ChoiceType normT normT_choiceMixin.
Definition normT_zmodMixin := Eval hnf in [zmodMixin of normT by <:].
Canonical normT_zmodType := Eval hnf in ZmodType normT normT_zmodMixin.
Definition normT_ringMixin := Eval hnf in [ringMixin of normT by <:].
Canonical normT_ringType := Eval hnf in RingType normT normT_ringMixin.
Definition normT_comRingMixin := Eval hnf in [comRingMixin of normT by <:].
Canonical normT_comRingType := Eval hnf in ComRingType normT normT_comRingMixin.
Definition normT_unitRingMixin := Eval hnf in [unitRingMixin of normT by <:].
Canonical normT_unitRingType := Eval hnf in UnitRingType normT normT_unitRingMixin.
Canonical normT_comUnitRingType := Eval hnf in [comUnitRingType of normT].
Definition normT_idomainMixin := Eval hnf in [idomainMixin of normT by <:].
Canonical normT_idomainType := Eval hnf in IdomainType normT normT_idomainMixin.
Definition normT_fieldMixin := Eval hnf in [fieldMixin of normT by <:].
Canonical normT_fieldType := Eval hnf in FieldType normT normT_fieldMixin.

Canonical normT_of_subType := Eval hnf in [subType of {normT T}].
Canonical normT_of_eqType := Eval hnf in [eqType of {normT T} ].
Canonical normT_of_choiceType := Eval hnf in [choiceType of {normT T}].
Canonical normT_of_zmodType := Eval hnf in [zmodType of {normT T}].
Canonical normT_of_ringType := Eval hnf in [ringType of {normT T}].
Canonical normT_of_comRingType := Eval hnf in [comRingType of {normT T}].
Canonical normT_of_unitRingType := Eval hnf in [unitRingType of {normT T}].
Canonical normT_of_comUnitRingType := Eval hnf in [comUnitRingType of {normT T}].
Canonical normT_of_idomainType := Eval hnf in [idomainType of {normT T}].
Canonical normT_of_fieldType := Eval hnf in [fieldType of {normT T}].

(* num structure *)

Lemma nval_inj : injective nval.
Proof. exact: val_inj. Qed.

Lemma nval_is_rmorphism : rmorphism nval.
Proof. by []. Qed.

Canonical nval_rmorphism := RMorphism nval_is_rmorphism.
Canonical nval_additive := Additive nval_is_rmorphism.

(* TODO généraliser à n'importe quelle fonction f vérifiant les bonnes hyp *)

Program Definition normT_LeMixin := (@RealLeMixin _ 
  (fun x y => (nval x) <= (nval y)) (fun x y => (nval x) < (nval y)) 
  (fun x => @NormT `| nval x | (normr_real (nval x))) _ _ _ _ _ _ _ _).
Obligation 1. by move=> x y; apply: addr_ge0. Qed.
Obligation 2. by move=> x y; apply: mulr_ge0. Qed.
Obligation 3. 
move=> [x x_re] /= H0x Hx0.
by apply/nval_inj/eqP => /=; rewrite eqr_le H0x Hx0.
Qed.
Obligation 4. by move=> x y; apply: subr_ge0. Qed.
Obligation 5. by move=> [x] /=; rewrite realE. Qed.
Obligation 6. by move=> [x x_re] /=; apply/nval_inj; rewrite /= normrN. Qed.
Obligation 7. 
by move=> [x x_re] /= H0x; apply/nval_inj; rewrite /= ger0_norm.
Qed.
Obligation 8. by move=> x y /=; rewrite ltr_def. Qed.

Canonical normT_numDomainType := Eval hnf in NumDomainType normT normT_LeMixin.
Canonical normT_numFieldType := Eval hnf in [numFieldType of normT].
Canonical normT_of_numDomainType := Eval hnf in [numDomainType of {normT T}].
Canonical normT_of_numFieldType := Eval hnf in [numFieldType of {normT T}].

Canonical normT_realDomainType := 
  Eval hnf in RealDomainType normT (RealLeAxiom normT_numDomainType).
Canonical normT_realFieldType := Eval hnf in [realFieldType of normT].
Canonical normT_of_realDomainType := Eval hnf in [realDomainType of {normT T}].
Canonical normT_of_realFieldType := Eval hnf in [realFieldType of {normT T}].

Definition rT := {normT T}.

Definition ext_f (f : {rmorphism realalg -> rT}) (x : complexalg) : T := 
  (nval (f (complex.Re x))) + 'i * (nval (f (complex.Im x))).

Lemma ext_f_is_rmorphism (f : {rmorphism realalg -> rT}) : rmorphism (@ext_f f).
Proof.
split.
+ move=> [xr xi] [yr yi]; rewrite /ext_f /= !rmorphB /= mulrBr opprD !addrA.
  by congr (_ + _); rewrite addrAC.
split; last by rewrite /ext_f /= rmorph0 rmorph1 mulr0 addr0.
move=> [xr xi] [yr yi]; rewrite /ext_f /= rmorphB !rmorphD !rmorphM !mulrDr /=.
rewrite !mulrDl ![_ * ('i * _)]mulrCA addrAC [X in (_ + X + _)]addrC !addrA.
by rewrite !mulrA; congr (_ + _ + _ + _); rewrite -expr2 sqrCi -mulrA mulN1r.
Qed.

Lemma conjM_real (x : T) : x * x^* \is Num.real.
Proof. by apply/ger0_real/mul_conjC_ge0. Qed.

Lemma conjD_real (x : T) : x + x^* \is Num.real.
Proof. by rewrite CrealE rmorphD conjCK addrC. Qed.

Lemma decomp_roots_poly (p : {poly normT}) :
  {l_re : seq normT & {l_im : seq T | 
    p = lead_coef p *: (\prod_(i <- l_re) ('X - i%:P) * 
                        \prod_(i <- l_im) ('X^2 - (NormT (conjD_real i)) *: 'X +
  (NormT (conjM_real i))%:P)) & forall x, x \in l_im -> irreducible_poly 
  ('X^2 - (NormT (conjD_real x)) *: 'X + (NormT (conjM_real x))%:P) }}.
Proof.
case: (boolP (p == 0)) => [/eqP -> | p_neq0].
  by exists [::]; exists [::]; rewrite //= lead_coef0 scale0r.
have := (leqnn (size p)); move: {2}(size p) => n; elim: n p p_neq0.
  by move=> p /negbTE p_neq0; rewrite leqn0 size_poly_eq0 p_neq0.
move=> n ihn p; case: (boolP (size p == n.+1)) => [/eqP H| /negbTE H]; last first.
  by rewrite leq_eqVlt H orFb ltnS => {H}; apply: ihn.
move=> p_neq0 _; case: n ihn H => [_ H | n ihn H].
  exists [::]; exists [::] => //=; rewrite !big_nil mulr1 alg_polyC lead_coefE.
  by rewrite H; apply: size1_polyC; rewrite H.
pose s := sroots (map_poly nval p); pose x := head 0 s.  
have x_root : root (map_poly nval p) x.
  apply/srootsP; first by rewrite map_poly_eq0 -size_poly_eq0 H.
  rewrite /x -nth0; apply/mem_nth; rewrite sroots_size.
  by rewrite map_poly_eq0 -size_poly_eq0 H /= size_map_poly H.
case: (boolP (x \is Num.real)) => [x_re | x_im].
  pose xn := NormT x_re; have := x_root; rewrite -[x]/(nval xn) -dvdp_XsubCl.
  have -> : 'X - (nval xn)%:P = map_poly nval ('X - xn%:P).
    by rewrite rmorphB /= map_polyX map_polyC /=.
  rewrite dvdp_map -eqp_div_XsubC; set q := _ %/ _ => /eqP Heqp.
  have q_neq0 : q != 0.
    by apply/negP => /eqP Hq; move/eqP: Heqp; rewrite Hq mul0r; apply/negP.
  have q_size : (size q <= n.+1)%N.
    have := H; rewrite Heqp size_Mmonic ?monicXsubC // size_XsubC addn2 /=.
    by move/eqP; rewrite eqSS leq_eqVlt => ->; rewrite orTb.
  have [l_re [l_im Hq Hirr]]:= (ihn q q_neq0 q_size).
  exists (xn :: l_re); exists l_im => //; rewrite Heqp big_cons.
  by rewrite lead_coef_Mmonic ?monicXsubC // -mulrA scalerAr -Hq mulrC.
have xC_root : root (map_poly nval p) x^*.
  have -> : map_poly nval p = map_poly (conjC \o nval) p.
    by apply: eq_map_poly => i /=; case: i => [i i_re] /=; rewrite conj_Creal.
  apply/rootP; rewrite map_poly_comp horner_map.
  by have /rootP -> := x_root; rewrite rmorph0.
pose rs := [:: x; x^*].
have Hmul a : map_poly nval ('X^2 - (NormT (conjD_real a)) *: 'X +
  (NormT (conjM_real a))%:P) = ('X - a%:P) * ('X - a^*%:P).
  rewrite rmorphD rmorphB /= map_polyC map_polyZ map_polyXn map_polyX /=.
  rewrite mulrBl !mulrBr expr2 -!addrA opprB; congr (_ + _).
  rewrite ['X * _]mulrC ![_ * 'X]mul_polyC [_ - _ in RHS]addrC addrA.
  rewrite [in _ *: _]addrC scalerDl opprD; congr (_ + _ + _).
  by rewrite -[RHS]mulr1 -mulrA mul_polyC mul_polyC scalerA alg_polyC.
pose q := 'X^2 - (NormT (conjD_real x)) *: 'X + (NormT (conjM_real x))%:P. 
have Hq : map_poly nval q = \prod_(i <- rs) ('X - i%:P).
  by rewrite /rs big_cons big_cons big_nil mulr1 /q Hmul.
have : (map_poly nval q %| map_poly nval p); last rewrite dvdp_map => q_div.
  rewrite Hq; apply: uniq_roots_dvdp; rewrite /rs ?uniq_rootsE /=.
    by rewrite x_root xC_root.
  by rewrite inE eq_sym -CrealE x_im.
have Heqr := (divpK q_div).
have r_neq0 : p %/ q != 0 by rewrite (dvdp_div_eq0 q_div) p_neq0.
have r_size : ((size (p %/ q)%R) <= n.+1)%N.
  have := H; rewrite -{1}Heqr size_Mmonic //; first last.
  + suff: map_poly nval q \is monic by rewrite map_monic.
    by rewrite Hq monic_prod // => i _; rewrite monicXsubC.
  have : size (map_poly nval q) = 3; last rewrite size_map_poly => ->.
    by rewrite Hq size_prod_XsubC /rs.
  by rewrite addn3 => /eqP /=; rewrite eqSS eqSS => /eqP ->.
have [l_re [l_im Hr Hirr]] := (ihn _ r_neq0 r_size).
exists l_re; exists (x :: l_im).
  rewrite -Heqr Hr lead_coefM lead_coefZ (_ : lead_coef (_ * _) = 1); last first.
    apply/eqP; rewrite -monicE rpredM ?rpred_prod // => i _.
      by apply: monicXsubC. 
    by rewrite -(map_monic nval_rmorphism) Hmul rpredM ?monicXsubC.
  rewrite mulr1 big_cons mulrCA [X in _ = _ *: X]mulrC -/q [in RHS]scalerAl.
  suff /eqP -> : lead_coef q == 1 by rewrite mulr1.
  by rewrite -monicE -(map_monic nval_rmorphism) Hmul rpredM ?monicXsubC.
move=> u; rewrite inE; case: (boolP (u == x)) => [/eqP -> _ | u_neqx ]; last first.
  by rewrite orFb; apply: Hirr.
apply: cubic_irreducible.
  by rewrite -(size_map_poly nval_rmorphism) Hq size_prod_XsubC /=.
move=> v; apply/negP => /(rmorph_root nval_rmorphism); rewrite Hq /=.
rewrite root_prod_XsubC !inE; case: v => [v v_re /=].
  case: (boolP (v == x)) => [/eqP Hv| _].
  by have := x_im; rewrite -Hv v_re.
rewrite orFb; case: (boolP (v == x^*)) => [/eqP | _ //].
rewrite -(conj_Creal v_re) => /(inv_inj (@conjCK _)) Hv.
by have := x_im; rewrite -Hv v_re.
Qed.

Lemma normT_real_closed : Num.real_closed_axiom normT_numFieldType.
Proof.
move=> f a b le_ab /andP[].
case: (boolP (root f a)) => [a_root _ _ | /negbTE a_nroot].
  by exists a => //; rewrite lerr le_ab.
rewrite ler_eqVlt -rootE a_nroot orFb => fa.
case: (boolP (root f b)) => [b_root _ | /negbTE b_nroot].
  by exists b => //; rewrite lerr le_ab.
rewrite ler_eqVlt eq_sym -rootE b_nroot orFb => fb.
(* R(i) alge closed -> f split en irreducible factor de deg 1 ou 2 *)
have [l_re [l_im eq_f irr_f]] := decomp_roots_poly f.
have root_l_re x : x \in l_re -> root f x.
  by move=> x_in; rewrite eq_f -mul_polyC !rootM root_prod_XsubC x_in /= orbT.
pose P2 (u v : normT) := ('X^2 + u *: 'X + v%:P).
have eq_P2 u v x : (x + u / 2%:R) ^+ 2 + (v - (u / 2%:R) ^+ 2) = (P2 u v).[x].
  rewrite /P2 !hornerD hornerXn hornerZ hornerX hornerC.
  rewrite sqrrD addrCA addrK addrC -mulr_natr mulrA mulfVK ?[u * x]mulrC //.
  by rewrite pnatr_eq0.
have size_P2 u v : size (P2 u v) = 3.
  rewrite /P2 -addrA size_addl ?size_polyXn //.
  apply/(leq_ltn_trans (size_add _ _) _); rewrite gtn_max size_polyC.
  suff: (size (u *: 'X) < 3)%N by case: (v != 0) => /=; rewrite andbT.
  by apply/(leq_ltn_trans (size_scale_leq _ _) _); rewrite size_polyX.
(* si p irred de degré 2 : p = x^2 + ax + b, et donc 4b > a donc p ne change pas de signe *)
have P2_pos u v x : irreducible_poly (P2 u v) -> (P2 u v).[x] > 0.
  move=> P2_irr; rewrite -eq_P2.
  have H y : ~~ (root (P2 u v) y).
    have [P2_size HP2] := P2_irr; apply/negP; rewrite -dvdp_XsubCl => Hdiv.
    have /HP2 H: (size ('X - y%:P)%R != 1)%N by rewrite size_XsubC.
    by have /H := Hdiv; rewrite -(dvdp_size_eqp Hdiv) size_XsubC size_P2.
  suff : (v - (u / 2%:R) ^+ 2) > 0.
    by rewrite -[X in _ -> X < _]addr0; apply: ler_lt_add; rewrite sqr_ge0.
  rewrite ltrNge -oppr_ge0; apply/negP; move Heq: (- (v - _)) => y.
  case: y Heq => [y y_re] Heq Hy; pose z := sqrtC y.
  have : 0 <= y by []; rewrite -sqrtC_ge0 -/z => Hz.
  have /negP := (H (NormT (ger0_real Hz) - (u / 2%:R))); apply; apply/rootP.
  rewrite -eq_P2 addrNK /=; apply/(nval_inj); rewrite rmorphD rmorphX.  
  by rewrite sqrtCK -[y]/(nval (NormT y_re)) -rmorphD -Heq addrC subrr.
have Hsg x : Num.sg f.[x] = 
             Num.sg (lead_coef f) * \prod_(i <- l_re) Num.sg ('X - i%:P).[x].
  rewrite [in LHS]eq_f hornerZ sgrM hornerM sgrM -[RHS]mulr1 mulrA. 
  congr (_ * _ * _); last rewrite big_seq_cond /=; last first.
    apply: (big_rec (fun i => Num.sg i.[x] = 1)); first by rewrite hornerE sgr1.
    move=> u p u_in Hp; rewrite hornerM sgrM Hp mulr1 -scaleNr -/(P2 (- _) _).
    apply/gtr0_sg/P2_pos; rewrite /P2 scaleNr.
    by apply: irr_f; move: u_in; rewrite andbT; apply.
  apply: (big_rec2 (fun i j => Num.sg i.[x] = j)).
    by rewrite hornerE sgr1.
  by move=> u p v _ Hp; rewrite hornerM sgrM Hp.
have : ~~ (Num.sg f.[a] == Num.sg f.[b]).
  rewrite (ltr0_sg fa) (gtr0_sg fb) eq_sym -subr_eq0 opprK /=.
  have -> : (1 + 1 = 2%:R :> normT) by rewrite -addn1 natrD.
  by rewrite pnatr_eq0.
have H : Num.sg (lead_coef f) != 0.
  rewrite sgr_eq0 lead_coef_eq0; apply/negP => /eqP f_eq0.
  by move: fa; rewrite f_eq0 horner0 ltrr.
rewrite !Hsg (inj_eq (mulfI H)) => /negP Hneq_prod.
have : has (fun i => (Num.sg ('X - i%:P).[a] == -1) && (Num.sg ('X - i%:P).[b] == 1)) l_re.
  apply/negPn/negP; rewrite -all_predC => /allP Hall; apply/Hneq_prod/eqP.
  rewrite big_seq_cond [in RHS]big_seq_cond. 
  apply: eq_bigr => i; rewrite andbT => i_in; have /= := (Hall i i_in).
  rewrite negb_and => /orP[]; case: (sgrP _) => //.
  + move/eqP; rewrite !hornerE subr_eq0 => /eqP eq_ai.
    by move: a_nroot; rewrite eq_ai (root_l_re _ i_in).
  + rewrite !hornerE => leq_ai _; apply/esym/gtr0_sg/(ltr_le_trans leq_ai).
    by apply/(ler_add le_ab (lerr _)).
  + by move=> _; rewrite eq_refl.
  + move/eqP; rewrite !hornerE subr_eq0 => /eqP eq_bi.
    by move: b_nroot; rewrite eq_bi (root_l_re _ i_in).
  + by move=> _; rewrite eq_refl.  
  + rewrite !hornerE => leq_bi _; apply/ltr0_sg/(ler_lt_trans _ leq_bi).
    by apply/(ler_add le_ab (lerr _)).
move/hasP => [x x_in]; rewrite !hornerE !sgr_cp0 => {Hsg} /andP[] Ha Hb.
exists x.
  by rewrite -subr_le0 -[X in _ && X]subr_ge0 (ltrW Ha) (ltrW Hb).
rewrite rootE eq_f !hornerE /= ?mulf_eq0; apply/orP; left; apply/orP; right.
rewrite horner_prod prodf_seq_eq0; apply/hasP; exists x => //.
by rewrite andTb !hornerE subrr.
Qed.

Canonical normT_rcfType := Eval hnf in RcfType normT normT_real_closed.
Canonical normT_of_rcfType := Eval hnf in [rcfType of {normT T}].

End NormRcfType.

Notation "{ 'normT' T }" := (normT_of (Phant T)).

Section NormArchiRcfType.

Variable T : archiNumClosedFieldType.

Lemma normT_archimedean : Num.archimedean_axiom (normT_numDomainType T).
Proof.
move=> x; have /archi_boundP := (normr_ge0 x); set n := bound _ => H.
by exists n; rewrite /Num.Def.ltr /= rmorph_nat; apply/(ltr_le_trans H).
Qed.

Canonical normT_archiNumDomainType :=
  ArchiNumDomainType (normT T) normT_archimedean.
Canonical normT_archiNumFieldType := [archiNumFieldType of normT T].
Canonical normT_archiRealDomainType := [archiRealDomainType of normT T].
Canonical normT_archiRealFieldType := [archiRealFieldType of normT T].
Canonical normT_archiRcfType := [archiRcfType of normT T].
Canonical normT_of_archiNumDomainType := [archiNumDomainType of {normT T}].
Canonical normT_of_archiNumFieldType := [archiNumFieldType of {normT T}].
Canonical normT_of_archiRealDomainType := [archiRealDomainType of {normT T}].
Canonical normT_of_archiRealFieldType := [archiRealFieldType of {normT T}].
Canonical normT_of_archiRcfType := [archiRcfType of {normT T}].

End NormArchiRcfType.

Section Algr.

Variable R : rcfType.

(* Useless : need uniform continuity *)
(* Lemma poly_cont_rat (x : rat) (p : {poly rat}) e : *)
(*   e > 0 -> exists2 d, d > 0 & forall (y : R), `|y - ratr x| < ratr d ->  *)
(*                 `|(map_poly ratr p).[y] - (map_poly ratr p).[ratr x]| < ratr e. *)
(* Proof. *)
(* elim/poly_ind: p e. *)
(*   by move=> e e0; exists 1=> // y; rewrite !rmorph0 !horner0 subrr normr0 ltr0q. *)
(* move=> p k; set pR := map_poly ratr p => Pp e e0. *)
(* pose ex := e / ((Num.max 1 `|x|) * 3%:R). *)
(* have ex0 : 0 < ex by rewrite pmulr_lgt0 // invr_gte0 pmulr_lgt0 ?ltr_maxr. *)
(* have [d d0 Hd] := Pp ex ex0. *)
(* pose ep := (e / ((Num.max 1 `|p.[x]|) * 3%:R)). *)
(* have ep0 : 0 < ep by rewrite pmulr_lgt0 // invr_gte0 pmulr_lgt0 ?ltr_maxr. *)
(* pose d' := Num.min (Num.min d (Num.max 1 `|x|)) ep. *)
(* have d'0 : d' > 0 by rewrite !ltr_minr d0 ep0 ?ltr_maxr. *)
(* exists d'; first exact: d'0. *)
(* move=> y yxd'; have /Hd Hpyx : `|y - ratr x| < ratr d. *)
(*   by apply/(ltr_le_trans yxd'); rewrite ler_rat !ler_minl lerr. *)
(* have Hmap z : (map_poly ratr (p * 'X + k%:P)).[z] = pR.[z] * z + ratr k. *)
(*   by rewrite rmorphD rmorphM /= map_polyC map_polyX !hornerE. *)
(* rewrite !Hmap opprD addrAC -addrA addrNK -[y in _ * y](addrNK (ratr x)). *)
(* rewrite mulrDr -addrA -mulrBl -{1}[pR.[y]](addrNK pR.[ratr x]) mulrDl. *)
(* apply/(@ltr_le_trans _ (ratr (e / 3%:R) + ratr (e / 3%:R) + ratr (e / 3%:R))); last first. *)
(*   by rewrite -!rmorphD ler_rat -addrA -mulr2n -mulrS -mulr_natr -ler_pdivl_mulr. *)
(* apply/(ler_lt_trans (ler_norm_add _ _))/ltr_add; last rewrite normrM. *)
(*   apply/(ler_lt_trans (ler_norm_add _ _))/ltr_add; rewrite normrM. *)
(*     apply/(ltr_le_trans (ltr_pmul (normr_ge0 _) (normr_ge0 _) Hpyx yxd')). *)
(*     rewrite -rmorphM ler_rat. *)
(*     have : d' <= (Num.max 1 `|x|) by rewrite !ler_minl lerr orbT. *)
(*     rewrite -(ler_pmul2l ex0) => /ler_trans; apply. *)
(*     rewrite /ex -mulrA invfM [_ / 3%:R]mulrC -mulrA mulVf ?mulr1 //. *)
(*     by apply/lt0r_neq0; rewrite ltr_maxr. *)
(*   rewrite horner_map /= -ratr_norm. *)
(*   case: (boolP (`|p.[x]| == 0)) => [/eqP -> | px_neq0]. *)
(*     by rewrite rmorph0 mul0r ltr0q ltr_pdivl_mulr ?mul0r. *)
(*   have /(ltr_le_trans _) : (ratr (`|p.[x]| * d') <= ratr (e / 3%:R) :> R). *)
(*     rewrite ler_rat; apply/(@ler_trans _ ((Num.max 1 `|p.[x]|) * d')). *)
(*       by rewrite ler_pmul2r ?d'0 // ler_maxr lerr orbT. *)
(*     rewrite minr_pmulr ?ler_maxr // ler_minl. *)
(*     apply/orP; right; rewrite mulrCA invfM [X in _ * X]mulrA divff //. *)
(*     by apply/lt0r_neq0; rewrite ltr_maxr. *)
(*   apply; rewrite [X in _ < X]rmorphM /= ltr_pmul2l ?yxd' //. *)
(*   by rewrite ltr0q ltr_neqAle eq_sym px_neq0 normr_ge0. *)
(* rewrite -ratr_norm; case: (boolP (`|x| == 0)) => [/eqP -> | x_neq0]. *)
(*   by rewrite rmorph0 mulr0 ltr0q ltr_pdivl_mulr ?mul0r. *)
(* have x_gt0 : (ratr `|x| > 0 :> R). *)
(*   by rewrite ltr0q ltr_neqAle eq_sym x_neq0 normr_ge0. *)
(* have := Hpyx; rewrite -(ltr_pmul2r x_gt0) => /ltr_le_trans; apply. *)
(* rewrite -rmorphM /= ler_rat -mulrA invfM mulrAC mulrC [X in X <= _]mulrA. *)
(* rewrite -[X in _ <= X]mulr1 (@ler_pmul2l _ (e / 3%:R)). *)
(*   by rewrite ler_pdivr_mull ?mulr1 ?ler_maxr ?lerr ?orbT // ltr_maxr. *)
(* by rewrite pmulr_lgt0 // invr_gte0. *)
(* Qed. *)

Import RealAlg.

Lemma poly_bound_rat {T : realFieldType} (p : {poly rat}) (a b : rat) :
  (cauchyreals.poly_bound (map_poly ratr p) (ratr a) (ratr b) =
  ratr (cauchyreals.poly_bound p a b) :> T).
Proof.
rewrite /cauchyreals.poly_bound size_map_poly rmorphD rmorph_sum rmorph1 /=.
congr (_ + _); apply/eq_bigr => i _; rewrite rmorphM rmorphX /= rmorphD /=.
by congr (_ * (_ + _) ^+ _); rewrite ratr_norm // -coef_map.
Qed.

Lemma poly_accr_bound_rat {T : realFieldType} (p : {poly rat}) (a b : rat) :
  (cauchyreals.poly_accr_bound (map_poly ratr p) (ratr a) (ratr b) =
  ratr (cauchyreals.poly_accr_bound p a b) :> T).
Proof.
rewrite /cauchyreals.poly_accr_bound size_map_poly.
rewrite rmorphM rmorphX rmorphD rmorph1 rmorph_sum /=.
congr (_ ^+ _ * (_ + _)).
  apply/eqP; rewrite eqr_le ler_maxr ler_maxl !mulr_natl -rmorphMn /=.
  rewrite (_ : (1 : T) = ratr 1) ; last by rewrite rmorph1.
  rewrite ![_ (Num.max 1 _) <= _]ler_rat !ler_maxl !lerr andbT /=.
  rewrite ![_ <= _ (Num.max 1 _)]ler_rat !ler_maxr !lerr orbT /=.
  by rewrite real_leVge // rpredMn ?num_real.
by apply/eq_bigr => i _; rewrite nderivn_map poly_bound_rat.
Qed.

Lemma ler_mid {T : realFieldType} (a b x : T) :
  (a <= x <= b) = (`|x - (b + a) / 2%:R| <= (b - a) / 2%:R).
Proof.
rewrite ler_norml ler_subr_addl -mulrBl ler_subl_addr -mulrDl.
have -> : (b + a - (b - a)) = a * 2%:R.
  by rewrite mulr_natr mulr2n opprB addrAC addrCA subrr addr0.
have -> : (b - a + (b + a)) = b * 2%:R.
  by rewrite mulr_natr mulr2n addrAC -!addrA subrr addr0.
by rewrite !mulfK // pnatr_eq0.
Qed.

Lemma ltr_mid {T : realFieldType} (a b x : T) :
  (a < x < b) = (`|x - (b + a) / 2%:R| < (b - a) / 2%:R).
Proof.
rewrite ltr_norml ltr_subr_addl -mulrBl ltr_subl_addr -mulrDl.
have -> : (b + a - (b - a)) = a * 2%:R.
  by rewrite mulr_natr mulr2n opprB addrAC addrCA subrr addr0.
have -> : (b - a + (b + a)) = b * 2%:R.
  by rewrite mulr_natr mulr2n addrAC -!addrA subrr addr0.
by rewrite !mulfK // pnatr_eq0.
Qed.

Lemma map_poly_pos {T : rcfType} (p : {poly rat}) (a b e : rat) :
  e > 0 -> (forall y, a <= y <= b -> p.[y] > e) ->
  forall (y : T), ratr a  <= y <= ratr b -> (map_poly ratr p).[y] > 0.
Proof.
move=> lt_e0 lt_p x /andP[]; rewrite ler_eqVlt => /orP[/eqP <- | lt_ax].
  rewrite ler_rat => le_ab; rewrite horner_map ltr0q.
  by apply/(ltr_trans lt_e0 (lt_p _ _)); rewrite lerr le_ab.
rewrite ler_eqVlt => /orP[/eqP eq_xb | lt_xb].
  rewrite eq_xb horner_map ltr0q; rewrite eq_xb ltr_rat in lt_ax.
  by apply/(ltr_trans lt_e0 (lt_p _ _)); rewrite lerr (ltrW lt_ax).
have lt_ab : a < b by have := (ltr_trans lt_ax lt_xb); rewrite ltr_rat.
have := (@cauchyreals.poly_accr_bound1P _ (map_poly ratr p) 
                             (ratr ((b + a) / 2%:R)) (ratr ((b - a) / 2%:R)) x).
set m := (_ / 2%:R); set r := (_ / 2%:R).
rewrite poly_accr_bound_rat; set k := _ p _ _; set k' := e / k => Hk.
have lt_k'0 : k' > 0 by apply/divr_gt0/cauchyreals.poly_accr_bound_gt0/lt_e0.
pose n := truncC ((b - a) / k').
pose n' := [arg max_(i > (@ord0 n) | x - ratr (a + k' * i%:R) >= 0) i].
have Pn'0 :  0 <= x - ratr (a + k' * (@ord0 n)%:R).
  by rewrite mulr0 addr0 subr_ge0 (ltrW lt_ax).
have /truncC_itv/andP[] : ((b - a) / k') >= 0.
  by apply/divr_ge0/(ltrW lt_k'0); rewrite subr_ge0 (ltrW lt_ab).
rewrite -/n => le_n gt_n; pose y := (a + k' * n'%:R).
have lt_ay : a <= y.
  by rewrite -ler_subl_addl subrr mulr_natr mulrn_wge0 // (ltrW lt_k'0).
have lt_yb : y <= b.
  rewrite -ler_subr_addl mulrC -ler_pdivl_mulr ?lt_k'0 //.
  apply/(ler_trans _ le_n); rewrite ler_nat /n'; case: arg_maxP => //.
  by move=> i _ _; rewrite -ltnS; apply/ltn_ord.
have Hym : `|ratr y - ratr m| <= ratr r :> T.
  by rewrite -rmorphB -ratr_norm ler_rat /r /m -ler_mid lt_ay lt_yb.
have Hxm : `|x - ratr m| <= ratr r.
  rewrite /m /r ![ratr (_ / 2%:R)]fmorph_div rmorphD rmorphB /= ratr_nat.
  by rewrite -ler_mid (ltrW lt_ax) (ltrW lt_xb).
have Hyx : (`|ratr y - x| <= ratr k' :> T).
  have Hle0 : ratr (a + k' * n'%:R) - x <= 0.
    by rewrite /n'; case: arg_maxP => // i Pi _; rewrite subr_le0 -subr_ge0.
  rewrite (ler0_norm Hle0) opprB /n'; case: arg_maxP => // im Pim Him.
  rewrite ler_subl_addl -rmorphD -addrA mulr_natr -mulrSr -mulr_natr /=.
  apply/ltrW; case: (boolP (im.+1 < n.+1)%N) => [ord_i | ].
    apply/negPn/negP; rewrite -lerNgt -subr_ge0 => H.
    by have /= := (Him (Ordinal ord_i)); move/(_ H); rewrite ltnn.
  rewrite -leqNgt ltnS leq_eqVlt leqNgt ltn_ord orbF => /eqP <-.
  apply/(ltr_trans lt_xb); rewrite ltr_rat -ltr_subl_addl -ltr_pdivr_mull //. 
  by rewrite mulrC gt_n.
have Hqd := (Hk _ Hxm Hym); have le_k0: ratr k >= 0 :> T. 
  by rewrite ler0q; apply/cauchyreals.poly_accr_bound_ge0.
have := (ler_trans Hqd (ler_pmul (normr_ge0 _) le_k0 Hyx (lerr _))).
rewrite -rmorphM /k' divfK /=; last first.
  by rewrite real_neqr_lt ?num_real // cauchyreals.poly_accr_bound_gt0 orbT.
rewrite ler_norml => /andP[_]; rewrite ler_subl_addr -ler_subl_addl.
move/(ltr_le_trans _); apply; rewrite subr_gt0 horner_map ltr_rat.
by apply/lt_p; rewrite lt_ay lt_yb.
Qed.

Lemma to_RP {T : numFieldType} (x : T) (a b : rat) (p : {poly rat}) (e : rat) :
  [/\ (ratr a <= x <= ratr b), (p.[a] <= 0 <= p.[b]), (root (map_poly ratr p) x)
       , (0 < e) & (forall y, a <= y <= b -> (p^`()).[y] > e)]  ->
  {u : R | (ratr a <= u <= ratr b) && (root (map_poly ratr p) u)}.
Proof.
move=> [] /andP[le_ax le_xb] /andP[].
have le_abR : (ratr a <= ratr b :> R).
  by have :=  (ler_trans le_ax le_xb); rewrite !ler_rat.
rewrite ler_eqVlt; case: (boolP (p.[a] == 0)) => [/eqP root_p _ pb0 | _ /= pa0].
  move=> _ _ _; exists (ratr a); rewrite lerr rootE horner_map le_abR /=.
  by rewrite fmorph_eq0 root_p.
rewrite ler_eqVlt; case: (boolP (0 == p.[b])) => [/eqP root_p _ | _ /= pb0].
  move=> _ _ _; exists (ratr b); rewrite lerr rootE horner_map le_abR /=.
  by rewrite fmorph_eq0 root_p.
move=> root_p lt_e0 der_p; pose q := (map_poly ratr p : {poly R}).
have q0_in : 0 \in `]q.[ratr a], q.[ratr b][.
  by rewrite inE !horner_map /= ltr0q ltrq0 pa0 pb0.
have [y |u [q_neg root_q u_in q_pos]] := (derp_root _ le_abR q0_in). 
  rewrite inE deriv_map /= => /andP[/ltrW lt_ay /ltrW lt_yb].
  by apply: (map_poly_pos lt_e0 der_p); rewrite lt_ay lt_yb.
exists u; apply/andP; split; last by apply/rootP/root_q.
by have := u_in; rewrite inE => /andP[/ltrW -> /ltrW ->].
Qed.

Lemma Q_dense_archi {T : archiRealFieldType} (x y : T) :
  x < y -> {q : rat | x < ratr q < y}.
Proof.
move=> lt_xy; pose e := y - x.
have lt_e0 : 0 < e by rewrite subr_gt0.
have lt_eI0 := (divr_ge0 ler01 (ltrW lt_e0)).
have := (archi_boundP lt_eI0); set n := bound _ => lt_n; have := lt_n.
have lt_n0 := (ler_lt_trans lt_eI0 lt_n).
rewrite (ltr_pdivr_mulr _ 1 lt_e0) mulrC -(ltr_pdivr_mulr _ _ lt_n0) => lt_e.
have /floorC_itv/andP[] : x * n%:R \is Num.real by apply: num_real.
set m := floorC _; rewrite -(ler_pdivr_mulr _ _ lt_n0) => le_rx.
rewrite -(ltr_pdivl_mulr _ _ lt_n0) => lt_xr; pose r := (m + 1)%:Q / n%:Q.
exists r; rewrite fmorph_div /= ratr_nat ratr_int lt_xr /= intrD mulrDl rmorph1.
by rewrite -(addrNK x y) -/e addrC; apply/(ltr_le_add lt_e le_rx).
Qed.

(* closed intervals instead of open ones  :TODO: change in polyrcf *)
Lemma deriv_sign_proper {T : rcfType} (a b : T) p :
  (forall x, x \in `]a, b[ -> p^`().[x] >= 0)
  -> (forall x y, (x \in `[a, b]) && (y \in `[a, b])
    ->  x < y -> p.[x] <= p.[y] ).
Proof.
move=> Pab x y; case/andP=> hx hy xy.
rewrite -subr_gte0; case: (@mvt _ x y p)=> //.
move=> c hc ->; rewrite pmulr_lge0 ?subr_gt0 ?Pab //.
by apply: subitvP hc; rewrite //= ?(itvP hx) ?(itvP hy).
Qed.

Definition BP_poly {T : archiRcfType} (x : T) (p : {poly rat}) :=
  if ((p != 0) && (root (map_poly ratr p) x))
    then let q := p %/ (gcdp p p^`()) in
         if ((map_poly ratr q)^`().[x] > 0)
           then q
           else -q
    else 0.

Lemma BP_poly_neq0 {T : archiRcfType} (x : T) (p : {poly rat}) :
  p != 0 -> (root (map_poly ratr p) x) -> (BP_poly x p) != 0.
Proof.
move=> p_neq0 root_p; rewrite /BP_poly p_neq0 root_p /=.
have H : p %/ gcdp p p^`() != 0 by rewrite dvdp_div_eq0 ?dvdp_gcdl ?p_neq0.
by case: ifP => _ //; rewrite oppr_eq0.
Qed.

(* :TODO: move and find a better proof : too long *)
(* should probably be on an idomain *)
Lemma mu_gcdp {T : fieldType} (p q : {poly T}) (x : T) :
  p * q != 0 -> \mu_x (gcdp p q) = minn (\mu_x p) (\mu_x q).
Proof.
move=> pq_n0; have := pq_n0; rewrite mulf_eq0 negb_or => /andP[p_n0 q_n0].
have g_n0 : gcdp p q != 0 by rewrite gcdp_eq0 (negbTE p_n0) (negbTE q_n0).
rewrite -[in minn _ _](divpK (dvdp_gcdr p q)) -[in minn _](divpK (dvdp_gcdl p q)).
rewrite !mu_mul ?divpK ?dvdp_gcdr ?dvdp_gcdl // -addn_minl -[LHS]add0n.
apply/eqP; rewrite eqn_add2r eq_sym -leqn0 geq_min.
case: (boolP (root (p %/ gcdp p q) x)) => [root_pg | /muNroot -> //].
have/coprimep_div_gcd/coprimep_root : (p != 0) || (q != 0) by rewrite p_n0.
by move/(_ _ root_pg); rewrite -rootE => /muNroot ->; rewrite leqnn orbT.
Qed.

(* :TODO: even longer than before (cf other dev or better_params) *)
Lemma BP_poly_root {T : archiRcfType} (x : T) (p : {poly rat}) :
  root (map_poly ratr (BP_poly x p)) x.
Proof.
rewrite /BP_poly; case: ifP => [/andP[pn0 rp]|_]; last by rewrite rmorph0 root0.
suff H : root (map_poly ratr (p %/ gcdp p p^`())) x.
  by case: ifP => _ //; rewrite rmorphN rootN /=.
rewrite map_divp gcdp_map -deriv_map /= -mu_gt0; set q := gcdp _ _; last first.
  by rewrite (dvdp_div_eq0 (dvdp_gcdl _ _)) map_poly_eq0 pn0.
have H : ((map_poly ratr p) != 0 :> {poly T}) by rewrite map_poly_eq0 pn0.
have := H; rewrite -[X in X != 0](divpK (dvdp_gcdl _ (map_poly ratr p)^`())).
move/(mu_mul x); rewrite (divpK (dvdp_gcdl _ _)) mu_gcdp; last first.
  apply/mulf_neq0; first by rewrite map_poly_eq0 pn0.
  rewrite -size_poly_eq0 -lt0n size_deriv /= -subn1 subn_gt0.
  by apply/(root_size_gt1 _ rp); rewrite map_poly_eq0 pn0.
move/eqP; rewrite -/q (mu_deriv_root H rp) -[X in minn _ X]addn0. 
by rewrite -addn_minr minn0 addn0 addnC eqn_add2r eq_sym => /eqP ->.
Qed. 

Lemma BP_poly_lt_q'0 {T : archiRcfType} (x : T) (p : {poly rat}) :
  p != 0 -> (root (map_poly ratr p) x) -> 
  (map_poly ratr (BP_poly x p))^`().[x] > 0.
Proof.
move=> pn0 root_p; have := BP_poly_root x p; rewrite /BP_poly pn0 root_p /=.
case: ifP => // /negbT.
rewrite -lerNgt ler_eqVlt => /orP[]; last first.
  by rewrite rmorphN derivN hornerN ltr_oppr oppr0.
rewrite -rootE deriv_map /= rmorphN rootN /=; set q := _ %/ _ => root_q' root_q.
have : map_poly ratr p != 0 :> {poly T} by rewrite map_poly_eq0.
move/separable.make_separable; rewrite /separable.separable_poly -/q.
rewrite deriv_map -gcdp_map -map_divp /= -/q => /coprimep_root /(_ root_q).
by rewrite -rootE deriv_map root_q'.
Qed.

Definition BP_eps {T : archiRcfType} (x : T) (p : {poly rat}) :=
  if ((p != 0
    then sval (Q_dense_archi (BP_poly_lt_q'0))
    else 0.
 
Lemma better_params {T : archiRcfType} (x : T) (p : {poly rat}) :
  p != 0 -> (root (map_poly ratr p) x) ->
  {a : rat & {b : rat & {e : rat & {q : {poly rat} | 
    [/\ (ratr a <= x <= ratr b), (q.[a] <= 0 <= q.[b]), (root (map_poly ratr q) x),
        (0 < e) & (forall y, a <= y <= b -> (q^`()).[y] > e)]}}}}.
Proof.
(* x should not be a root of p^`() *)
wlog: p / separable.separable_poly p.
  move=> ihp p_n0 root_p.
  pose ps := p %/ (gcdp p p^`()).
  have lc_n0 : lead_coef (gcdp p p^`()) != 0.
    by rewrite lead_coef_eq0 gcdp_eq0 negb_and p_n0. 
  have eq_p := (divpK (dvdp_gcdl p (deriv p))).
  have ps_n0 : ps != 0.
    apply/negP => /eqP eq_ps; have:= eq_p; rewrite -/ps eq_ps mul0r.
    by move/esym; apply/eqP/p_n0.
  have root_ps : root (map_poly ratr ps) x.
    rewrite /ps -mu_gt0; last first.
      rewrite map_poly_eq0; apply/negP => /eqP H; rewrite H mul0r in eq_p.
      by rewrite -eq_p eq_refl in p_n0.
    rewrite -(ltn_add2r (\mu_x (map_poly ratr (gcdp p p^`())))) add0n -mu_mul //.
      rewrite -rmorphM /= divpK ?dvdp_gcdl //.
      rewrite (mu_deriv_root _ root_p) ?map_poly_eq0 // addn1 ltnS /=. 
      rewrite gcdp_map deriv_map /=.
      have H := (divpK (dvdp_gcdr (map_poly ratr p) (map_poly ratr p^`()))).
      rewrite -{2}H mu_mul ?leq_addl // H -size_poly_eq0 -deriv_map size_deriv.
      rewrite -lt0n -ltnS prednK; last by rewrite lt0n size_poly_eq0 map_poly_eq0.
      by apply: (root_size_gt1 _ root_p); rewrite map_poly_eq0.
    by apply/mulf_neq0; rewrite map_poly_eq0 -?/ps ?ps_n0 -?lead_coef_eq0 ?lc_n0.
  have sep_ps : separable.separable_poly ps by apply/separable.make_separable.
  by apply/(ihp ps sep_ps ps_n0 root_ps).
(* p^`() should be positive on x *)
wlog : p / (map_poly ratr p)^`().[x] > 0 => [ihp | ].
  case: (ltrgt0P (map_poly ratr p)^`().[x]); first by apply: ihp.
    move=> p_neg p_sep p_n0 root_p; apply: (ihp (-p)) => //.
    + by rewrite rmorphN derivN hornerN oppr_gt0 /= p_neg.
    + have := p_sep; rewrite /separable.separable_poly derivN /coprimep.
      rewrite -mulN1r -[- p^`()]mulN1r -(eqp_size (mulp_gcdr _ _ _)) mulN1r.
      by rewrite size_opp.
    + by rewrite oppr_eq0.
    by rewrite rmorphN rootN.
  move=> root_p' p_sep p_n0 root_p.
  have pm_sep : separable.separable_poly (map_poly ratr p : {poly T}). 
    by rewrite separable.separable_map.
  by have := (coprimep_root pm_sep root_p); rewrite root_p' eq_refl.
move=> lt_p'x _ p_neq0 root_p.
have : {u : rat & {v : rat & {e : rat | [/\ e > 0, ratr u < x < ratr v & 
       forall y : rat, u <= y <= v -> e < (p^`()).[y]]}}}.
  have [e /andP[lt_e0 lt_ep'x]] := Q_dense_archi lt_p'x.
  have Hh a : ratr a / 2%:R = ratr (a / 2%:R) :> T.
    by rewrite fmorph_div /= ratr_nat.
  have p'_n0 : (map_poly ratr p^`()) != 0 :> {poly T}.
    by apply/negP => /eqP H; have := lt_p'x; rewrite deriv_map H horner0 ltrr.
  pose q := (map_poly ratr p)^`() - (ratr e)%:P : {poly T}.
  have q_n0 : q != 0.
    rewrite /q; apply/negP=> /eqP /(congr1 (fun i => i.[x])).
    by rewrite !hornerE => H; have := lt_ep'x; rewrite -subr_gt0 H ltrr.
  have lt_1x: (x - 1 < x) by rewrite ltr_subl_addr -ltr_subl_addl subrr ltr01.
  have := (prev_root_lt lt_1x q_n0); set u := prev_root _ _ _. 
  move/Q_dense_archi => [a /andP[lt_ua lt_ax]]; rewrite ltr_subl_addr in lt_1x.
  have := (next_root_gt lt_1x q_n0); set v := next_root _ _ _.
  move/Q_dense_archi => [b /andP[lt_xb lt_bv]]; rewrite -ltr_subl_addr in lt_1x.
  exists a; exists b; exists e; split; first by have := lt_e0; rewrite ltr0q.
    by rewrite lt_ax lt_xb.
  have nroot_pe : ~~ root q x.
    by rewrite rootE !hornerE subr_eq0 eqr_le negb_and -ltrNge lt_ep'x.
  have sgr_pn : Num.sg q.[x] = 1.
    by apply/eqP; rewrite sgr_cp0 !hornerE subr_gt0 lt_ep'x.
  move=> y /andP[le_ay le_yb].
  case: (ltrgtP (ratr y) x) => [lt_yx | lt_xy | eq_yx].
  + have lt_uy: u < ratr y by apply: (ltr_le_trans lt_ua); rewrite ler_rat.
    have := sgr_pn; rewrite -(@sgr_neighplN _ _ (x - 1) _ nroot_pe (ratr y)).
    by move/eqP; rewrite sgr_cp0 !hornerE subr_gt0 deriv_map horner_map ltr_rat.
    by rewrite /neighpl inE -/u lt_uy lt_yx.
  + have lt_yv: ratr y < v by apply: (ler_lt_trans _ lt_bv); rewrite ler_rat.
    move: nroot_pe; rewrite rootE => nroot_pe; have := sgr_pn.
    rewrite -(@sgr_neighprN _ _ _ (x + 1) nroot_pe (ratr y)); last first.
      by rewrite /neighpr inE -/v lt_yv lt_xy.
    by move/eqP; rewrite sgr_cp0 !hornerE subr_gt0 deriv_map horner_map ltr_rat.
  by have := lt_ep'x; rewrite -eq_yx deriv_map horner_map ltr_rat.
move=> [u [v [e [lt_e0 /andP[lt_ux lt_xv] He]]]]; have /rootP px := root_p.
exists u; exists v; exists e; exists p.
split => //; rewrite ?(ltrW lt_ux) ?(ltrW lt_xv) //.
have /deriv_sign_proper H0 : forall y : T, y \in `](ratr u),(ratr v)[ -> 
                        0 <= ((map_poly ratr p)^`()).[y]. 
  move=> y; rewrite inE => /andP[lt_uy lt_yv]; apply/ltrW; rewrite deriv_map.
  by apply/(map_poly_pos lt_e0 He); rewrite (ltrW lt_uy) (ltrW lt_yv).
apply/andP; split.
  case: (boolP (x == ratr u)) => [/eqP eq_xu | neq_xu].
    have: (map_poly ratr p).[ratr u] == 0 :> T by rewrite -eq_xu px.
    by rewrite horner_map /= fmorph_eq0 => /eqP ->; rewrite lerr.
  have := (H0 (ratr u) x); rewrite px horner_map lerq0 => -> //=.
  by rewrite !inE lerr (ltrW lt_ux) (ltrW lt_xv) (ltrW (ltr_trans lt_ux lt_xv)).
case: (boolP (x == ratr v)) => [/eqP eq_xv | neq_xv].
  have: (map_poly ratr p).[ratr v] == 0 :> T by rewrite -eq_xv px.
  by rewrite horner_map /= fmorph_eq0 => /eqP ->; rewrite lerr.
have := (H0 x (ratr v)); rewrite px horner_map ler0q => -> //=.
by rewrite !inE lerr (ltrW lt_ux) (ltrW lt_xv) (ltrW (ltr_trans lt_ux lt_xv)).
Qed.

(* Lemma to_algdom_mid {F : archiRealFieldType} (x : {alg F}): *)
(*   let y := to_algdom (repr x) in  *)
(*   let c := center_alg y in *)
(*   let r := radius_alg y in *)
(*   (c - r)%:RA <= x <= (c + r)%:RA. *)
(* Proof. *)
(* have H /= : \pi_({alg F})%qT (repr x) = x by rewrite reprK. *)
(* rewrite -[X in _ <= X <= _]H; move: (repr x) => y {H x}; rewrite !piE. *)
(* have Hy := (@to_algdomK _ y); apply/andP. *)
(* rewrite -(and_iff_compat_r _ (rwP (le_algP _ _))). *)
(* rewrite -(and_iff_compat_l _ (rwP (le_algP _ _))). *)
(* rewrite /cauchyreals.le_creal. *)
(* rewrite -(cauchyreals.lt_creal_morph Hy (@cauchyreals.eq_creal_refl _ _)). *)
(* rewrite -(cauchyreals.lt_creal_morph (@cauchyreals.eq_creal_refl _ _) Hy). *)
(* have H (T : archiFieldType) (x : T) i : (0 <= x / 2%:R ^+ i) = (0 <= x).  *)
(*   by rewrite ler_pdivl_mulr ?mul0r // exprn_gt0 ?ltr0n. *)
(* have H2 (T : archiFieldType) (x : T) n :  *)
(*   (x / 2%:R ^+ n.+1 + x / 2%:R ^+ n.+1 = x / 2%:R ^+ n :> T). *)
(*   rewrite -mulrDl -mulr2n -mulr_natr -mulrA -[X in _ * X = _]invrK invf_div. *)
(*   by rewrite exprS mulrAC divff ?pnatr_eq0 // mul1r. *)
(* have Hj : forall j : nat, (cauchyreals.cauchyseq (to_algcreal (to_algdom y)) j <=  *)
(*          (center_alg (to_algdom y) +  *)
(*           (\sum_(0 <= i < j) (radius_alg (to_algdom y)) / 2%:R ^+ i.+1)) /\ *)
(*          (center_alg (to_algdom y) -  *)
(*           (\sum_(0 <= i < j) (radius_alg (to_algdom y)) / 2%:R ^+ i.+1)) *)
(*         <= cauchyreals.cauchyseq (to_algcreal (to_algdom y)) j). *)
(*   move=> j /=; unlock to_algcreal; rewrite /=; elim : j => [|n ]. *)
(*     by rewrite /= big_geq // subr0 addr0 lerr. *)
(*   set p := to_algcreal_of _ _ _ n; move => [] Hinf Hsup /=. *)
(*   case: ifP => _; rewrite -/p; split. *)
(*   + rewrite (big_nat_recr _ _ (fun i => radius_alg (to_algdom y) / 2%:R ^+ i.+1)) //. *)
(*     rewrite /= ler_subl_addr addrA -[_ + _ + _ + _]addrA -mulr2n //. *)
(*     apply/(ler_trans Hinf); rewrite -ler_subl_addl subrr. *)
(*     by apply/mulrn_wge0/divr_ge0/exprn_ge0/ler0n/radius_alg_ge0. *)
(*   + rewrite ler_subl_addr addrAC. *)
(*     rewrite (big_nat_recr _ _ (fun i => radius_alg (to_algdom y) / 2%:R ^+ i.+1)) //=. *)
(*     by rewrite -!addrA subrr addr0 -ler_subl_addr Hsup. *)
(*   + rewrite (big_nat_recr _ _ (fun i => radius_alg (to_algdom y) / 2%:R ^+ i.+1)) //=. *)
(*     by rewrite -ler_subr_addr addrA -!addrA subrr addr0 Hinf. *)
(*   rewrite ler_subl_addl. *)
(*   rewrite (big_nat_recr _ _ (fun i => radius_alg (to_algdom y) / 2%:R ^+ i.+1)) //=. *)
(*   rewrite -!addrA -ler_subl_addl. *)
(*   apply/(ler_trans Hsup); rewrite addrCA -ler_subl_addl subrr -mulr2n. *)
(*   by apply/mulrn_wge0/divr_ge0/exprn_ge0/ler0n/radius_alg_ge0. *)
(* have Hsum j : \sum_(0 <= i < j) (radius_alg (to_algdom y) / 2%:R ^+ i.+1) <=  *)
(*               radius_alg (to_algdom y). *)
(*   rewrite -big_distrr /= ler_pimulr ?radius_alg_ge0 //. *)
(*   set u := 2%:R; rewrite big_nat. *)
(*   rewrite (eq_bigr (fun i => u ^- j * u ^+ (0 + j - i.+1))); last first. *)
(*     move=> i /andP[_ lt_ij]; rewrite expfB_cond; last first. *)
(*       by rewrite pnatr_eq0 /= add0n. *)
(*     rewrite mulrCA mulrA divff ?mul1r //.   *)
(*     by rewrite expf_eq0 pnatr_eq0 negb_and /= orbT. *)
(*   rewrite -big_nat -big_distrr /= -ler_pdivl_mull; last first. *)
(*     by rewrite invr_gt0 exprn_gt0 ?ltr0n. *)
(*   rewrite invrK mulr1 -(big_nat_rev _ 0%N j xpredT (fun i => u ^+ i)) /=. *)
(*   elim: j => [| j ihj]; first by rewrite big_geq // exprn_ge0 ?ler0n. *)
(*   rewrite (big_nat_recr j 0%N (fun i => u ^+ i) (leq0n _)) /= -ler_subr_addr. *)
(*   by apply/(ler_trans ihj); rewrite ler_subr_addr -mulr2n -mulr_natr exprS mulrC. *)
(* split; apply/(@cauchyreals.le_crealP _ 0%N)=> j _ /=. *)
(*   have [Hsup Hinf] := (Hj j); apply/(ler_trans _ Hinf).  *)
(*   by rewrite ler_subr_addl addrA ler_subl_addl ler_add2r Hsum. *)
(* by have [Hsup Hinf] := (Hj j); apply/(ler_trans Hsup); rewrite ler_add2l Hsum. *)
(* Qed.   *)

(* Lemma to_algdom_mid_ratr (x : realalg) : *)
(*   let y := to_algdom (repr x) in  *)
(*   ratr (center_alg y - radius_alg y) <= x <= ratr (center_alg y + radius_alg y). *)
(* Proof. by have := (to_algdom_mid x) => /=; rewrite !fmorph_eq_rat. Qed. *)

(*Lemma better_params {T : archiRcfType} (x : T) (p : {poly rat}) :
  p != 0 -> (root (map_poly ratr p) x) ->
  {a : rat & {b : rat & {e : rat & {q : {poly rat} | 
    [/\ (ratr a <= x <= ratr b), (q.[a] <= 0 <= q.[b]), (root (map_poly ratr q) x),
        (0 < e) & (forall y, a <= y <= b -> (q^`()).[y] > e)]}}}}.*)

Definition BP_inf {T : archiRcfType} x (p : {poly rat}) p_neq0 root_p :=
  tag (@better_params T x p p_neq0 root_p).
Definition BP_sup {T : archiRcfType} x (p : {poly rat}) p_neq0 root_p :=
  tag (tagged (@better_params T x p p_neq0 root_p)).
Definition BP_eps {T : archiRcfType} x (p : {poly rat}) p_neq0 root_p :=
  tag (tagged (tagged (@better_params T x p p_neq0 root_p))).
Definition BP_poly {T : archiRcfType} x (p : {poly rat}) p_neq0 root_p :=
  tag (tagged (tagged (tagged (@better_params T x p p_neq0 root_p)))).
Definition BP_cond {T : archiRcfType} x (p : {poly rat}) p_neq0 root_p :=
  tagged (tagged (tagged (tagged (@better_params T x p p_neq0 root_p)))).

Ltac BP_simpl :=
  rewrite ?/BP_inf ?/BP_sup ?/BP_eps ?/BP_poly ?/BP_cond.
Ltac to_BP :=
  rewrite -?/BP_inf -?/BP_sup -?/BP_eps -?/BP_poly -?/BP_cond.

Lemma BP_le_x {T : archiRcfType} (x : T) p p_neq0 (root_p : root (map_poly ratr p) x):
  ratr (BP_inf p_neq0 root_p) <= x <= ratr (BP_sup p_neq0 root_p).
Proof. by have [] := BP_cond p_neq0 root_p. Qed.
  BP_simpl.  
rewrite -/BP_inf.

Lemma root_annul_realalg_ratr (x : realalg) :
  root (map_poly ratr (annul_realalg x)) x.
Proof.
by have := (root_annul_realalg x); rewrite (eq_map_poly (fmorph_eq_rat _)).
Qed.

Definition realalg_to_R (x : realalg) := 
  let P := better_params (annul_realalg_neq0 x) (root_annul_realalg_ratr x) in
  sval (to_RP (tagged (tagged (tagged (tagged P))))).

Lemma minCpoly_neq0_rat (x : {normT algC}) :
  tag (minCpolyP (nval x)) != 0.
Proof. by have [[_ /monic_neq0]] := tagged (minCpolyP (nval x)). Qed.

Lemma root_minCpoly_rat_norm (x : {normT algC}) :
  root (map_poly ratr (tag (minCpolyP (nval x)))) x.
Proof. 
set u := @nval _; have [[H _ _]]:= tagged (minCpolyP (nval x)); move: H.
have /eq_map_poly <- : u \o ratr =1 ratr by apply/fmorph_eq_rat.
move=> H; have := (root_minCpoly (nval x)); rewrite {1}H map_poly_comp.
by rewrite !rootE /= horner_map /=.
Qed.

Definition normTalgC_to_R (x : {normT algC}) :=
  let P := better_params (minCpoly_neq0_rat x) 
                         (root_minCpoly_rat_norm x) in 
  sval (to_RP (tagged (tagged (tagged (tagged P))))).

Lemma realalg_to_R_is_rmorphism : rmorphism realalg_to_R.
Proof.
split; last first.
+ split; last first.
    rewrite /realalg_to_R; set BP := better_params _ _.
    have := svalP (to_RP (tagged (tagged (tagged (tagged BP))))).
    set xR := sval _.
    have := (tagged (tagged (tagged (tagged BP)))).
    set a := tag BP; set b := tag (tagged BP).
    set e := tag (tagged (tagged BP)).
    set q := tag (tagged (tagged (tagged BP))) => [[]].





+ move=> x y.


  








End Algr.