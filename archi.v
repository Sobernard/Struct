(* (c) Copyright 2006-2017 Microsoft Corporation and Inria.                   *)
(* Distributed under the terms of CeCILL-B.                                   *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import ssrint rat algC realalg poly complex.
From mathcomp Require Import polyorder polydiv interval polyrcf.

(******************************************************************************)
(* This file defines structures for archimedean integral domains and fields   *)
(* equipped with a partial order and a norm.                                  *)
(*                                                                            *)
(*    * ArchiNumDomain (archimedean NumDomain)                                *)
(*  archiNumDomainType == interface for an archimedean num integral domain.   *)
(* ArchiNumDomainType T a                                                     *)
(*                     == packs the archimedean axiom a into an               *)
(*                        archiNumDomainType. The carrier T must have a num   *)
(*                        domain structure.                                   *)
(* [archiNumDomainType of T for S ]                                           *)
(*                     == T-clone of the archiNumDomainType structure of S.   *)
(* [archiNumDomainType of T]                                                  *)
(*                     == clone of a canonical archiNumDomainType structure   *)
(*                        on T.                                               *)
(*                                                                            *)
(*    * ArchiNumField (archimedean NumField)                                  *)
(*   archiNumFieldType == interface for an archimedean num field.             *)
(* ArchiNumFieldType T a                                                      *)
(*                     == packs the archimedean axiom a into an               *)
(*                        archiNumFieldType. The carrier T must have a num    *)
(*                        field structure.                                    *)
(* [archiNumFieldType of T]                                                   *)
(*                     == clone of a canonical archiNumFieldType structure    *)
(*                        on T.                                               *)
(*                                                                            *)
(*    * ArchiNumClosedField (archimedean NumClosedField)                      *)
(* archiNumClosedFieldType                                                    *)
(*                     == interface for an archimedean num closed field.      *)
(* ArchiNumClosedFieldType T a                                                *)
(*                     == packs the archimedean axiom a into an               *)
(*                        archiNumClosedFieldType. The carrier T must have a  *)
(*                        num closed field structure.                         *)
(* [archiNumClosedFieldType of T]                                             *)
(*                     == clone of a canonical archiNumClosedFieldType        *)
(*                        structure on T.                                     *)
(*                                                                            *)
(*    * ArchiRealDomain (archimedean RealDomain)                              *)
(*  archiRealDomainType == interface for an archimedean real integral domain. *)
(* ArchiRealDomainType T a                                                    *)
(*                     == packs the archimedean axiom a into an               *)
(*                        archiRealDomainType. The carrier T must have a real *)
(*                        domain structure.                                   *)
(* [archiRealDomainType of T]                                                 *)
(*                     == clone of a canonical archiRealDomainType structure  *)
(*                        on T.                                               *)
(*                                                                            *)
(*    * ArchiRealField (archimedean RealField)                                *)
(*  archiRealFieldType == interface for an archimedean real field.            *)
(* ArchiRealFieldType T a                                                     *)
(*                     == packs the archimedean axiom a into an               *)
(*                        archiRealFieldType. The carrier T must have a real  *)
(*                        field structure.                                    *)
(* [archiRealFieldType of T]                                                  *)
(*                     == clone of a canonical archiRealFieldType structure   *)
(*                        on T.                                               *)
(*                                                                            *)
(*    * ArchiNumClosedField (archimedean NumClosedField)                      *)
(*        archiRcfType == interface for an archimedean num closed field.      *)
(*    ArchiRcfType T a == packs the archimedean axiom a into an               *)
(*                        archiNumClosedFieldType. The carrier T must have a  *)
(*                        num closed field structure.                         *)
(* [archiRcfType of T] == clone of a canonical archiNumClosedFieldType        *)
(*                        structure on T.                                     *)
(*                                                                            *)
(* NumClosedField structures can be given a total order :                     *)
(* x <=%C y ==                                                                *)
(*                                                                            *)
(*                                                                            *)
(* Over these structures, we have the following operations :                  *)
(*     Cnat == the subset of natural integers.                                *)
(*     Cint == the subset of integers.                                        *)
(* truncC z == for z >= 0, an n : nat s.t. n%:R <= z < n.+1%:R, else 0%N.     *)
(* floorC z == for z \in Num.real, an m : int s.t. m%:~R <= z <= (m + 1)%:~R. *)
(* These are explicitly instanciated for int (Znat), rat (Qnat, Qint) and     *)
(* algC (Cnat, Cint).                                                         *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Module Archi.

Local Notation num_for T b := (@Num.NumDomain.Pack T b T).

(* Archimedean num structures *)
Module ArchiNumDomain.

Section ClassDef.

Record class_of R := Class {base : Num.NumDomain.class_of R; 
                            _ : @Num.archimedean_axiom (num_for R base)}.
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
  (at level 0, format "[ 'archiNumDomainType'  'of'  T  'for'  cT ]") 
                                                       : form_scope.
Notation "[ 'archiNumDomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'archiNumDomainType'  'of'  T ]") : form_scope.
End Exports.

End ArchiNumDomain.
Import ArchiNumDomain.Exports.

Module ArchiNumField.

Section ClassDef.

Record class_of R := Class { base : Num.NumField.class_of R; 
                             mixin : @Num.archimedean_axiom (num_for R base) }.
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
Definition join_archiNumDomainType := 
  @ArchiNumDomain.Pack numFieldType xclass xT.

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

Record class_of R := Class { base : Num.ClosedField.class_of R; 
                             mixin : @Num.archimedean_axiom (num_for R base) }.
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
  fun bT b & phant_id (Num.ClosedField.class bT)
                      (b : Num.ClosedField.class_of T) =>
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


(* Archimedean real structures *)
Module ArchiRealDomain.

Section ClassDef.

Record class_of R := Class {base : Num.RealDomain.class_of R; 
                            mixin : @Num.archimedean_axiom (num_for R base)}.
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
  fun bT b & phant_id (Num.RealDomain.class bT) (b : Num.RealDomain.class_of T) 
    =>
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
Definition join_archiNumDomainType :=
  @ArchiNumDomain.Pack realDomainType xclass xT.

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

Record class_of R := Class { base : Num.RealField.class_of R; 
                             mixin : @Num.archimedean_axiom (num_for R base) }.
Definition base2 R (c : class_of R) := ArchiNumField.Class (@mixin R c).
Local Coercion base : class_of >-> Num.RealField.class_of.
Definition base3 R (c : class_of R) := @ArchiRealDomain.Class _ c (@mixin _ c). 
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
Definition join_archiRealDomainType := 
  @ArchiRealDomain.Pack realDomainType xclass xT.
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

Record class_of R := Class { base : Num.RealClosedField.class_of R; 
                             mixin : @Num.archimedean_axiom (num_for R base) }.
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
  fun bT b & phant_id (Num.RealClosedField.class bT) 
                      (b : Num.RealClosedField.class_of T) =>
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
Implicit Types (x y z : R) (nu : {rmorphism R -> R}).

(* nat subset *)
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

(* int subset *)
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

(* relation between Cint and Cnat. *)
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

(* relation between truncC and oldtruncC. *)
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


(* int is archimedean *)
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
Canonical Znat_keyed := KeyedQualifier Znat_key.

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

(* relation between Znat and oldZnat. *)
Lemma Znat_old (m : int) : (m \is a Znat) = (m \is a ssrint.Znat).
Proof. by apply/ZnatP/ssrint.ZnatP. Qed.

End ZnatPred.


(* rat is archimedean *)
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

(* relation between Qint and oldQint. *)
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

(* relation between Qnat and oldQnat. *)
Lemma Qnat_old (x : rat) : (x \is a Qnat) = (x \is a rat.Qnat).
Proof. by apply/QnatP/rat.QnatP. Qed.

Fact Qnat_semiring_closed : semiring_closed Qnat.
Proof. exact: (Cnat_semiring rat_archiRealField). Qed.
Canonical Qnat_addrPred := AddrPred Qnat_semiring_closed.
Canonical Qnat_mulrPred := MulrPred Qnat_semiring_closed.
Canonical Qnat_semiringPred := SemiringPred Qnat_semiring_closed.

End QnatPred.

(* :TODO:
Lemma Qint_dvdz (m d : int) : (d %| m)%Z -> ((m%:~R / d%:~R : rat) \is a Qint).

Lemma Qnat_dvd (m d : nat) : (d %| m)%N → ((m%:R / d%:R : rat) \is a Qnat).

+ locate other occurences
*)

(* algC is archimedean *)
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

(* relation between Cint and oldCint. *)
Lemma Cint_old (x : algC) : (x \is a Cint) = (x \in Algebraics.Exports.Cint).
Proof. by apply/CintP/algC.CintP. Qed.

(* relation between Cnat and oldCnat. *)
Lemma Cnat_old (x : algC) : (x \is a Cnat) = (x \in Algebraics.Exports.Cnat).
Proof. by apply/CnatP/algC.CnatP. Qed.

End algCPred.


Section NCFComplements.

Variable R : numClosedFieldType.
Implicit Types x y : R.

(* complete order not compatible with all operations ! *)
Definition lec x y :=
    ('Re x < 'Re y) || (('Re x == 'Re y) && ('Im x <= 'Im y)).

Definition ltc x y :=
    (lec x y) && (x != y).

Notation "x <=%C y" := (lec x y) (at level 35) : ring_scope. 
Notation "x <%C y" := (ltc x y) (at level 35) : ring_scope.

Lemma lecE x y : 
  (x <=%C y) = ('Re x < 'Re y) || (('Re x == 'Re y) && ('Im x <= 'Im y)).
Proof. by rewrite /lec. Qed.

Lemma ltcE x y :
  (x <%C y) = (x <=%C y) && (x != y).
Proof. by rewrite /ltc. Qed.

Lemma lecc : reflexive lec.
Proof. by move=> x; rewrite lecE eq_refl lerr andbT orbT. Qed.
Hint Resolve lecc.

Lemma lec_trans : transitive lec.
Proof.
move=> x y z; rewrite !lecE => /orP[Ryx | /andP[/eqP <- Iyx]].
  move=> /orP[Rxz | /andP[/eqP <- _]].
  + by apply/orP; left; apply: (ltr_trans Ryx Rxz).
  + by rewrite Ryx.
move=> /orP[Ryz | /andP[/eqP <- Ixz]].
+ by rewrite Ryz.
+ by rewrite eq_refl (ler_trans Iyx Ixz) andbT orbT.
Qed.

Lemma lec_asym : antisymmetric lec.
Proof.
move=> x y /andP[]; rewrite !lecE => /orP[Rxy | /andP[/eqP Rxy Ixy /=]].
  move=> /orP[ | /andP[]].
  + by rewrite ltr_gtF.
  by rewrite (gtr_eqF Rxy).
move=> /orP[ | /andP[/eqP Ryx Iyx]].
+ by rewrite Rxy ltrr.
rewrite [x]Crect [y]Crect Rxy.
by move: Iyx; rewrite ler_eqVlt (ler_gtF Ixy) orbF => /eqP ->.
Qed.

Lemma ltc_neqAle x y :
  (x <%C y) = (x != y) && (x <=%C y).
Proof. by rewrite ltcE andbC. Qed.

Lemma lec_eqVlt x y :
  (x <=%C y) = (x == y) || (x <%C y).
Proof.
rewrite ltc_neqAle.
by case: (boolP (x == y)) => [/eqP -> | _ //=]; rewrite orTb lecc.
Qed.

Lemma ltcNge x y : x <%C y = ~~ (y <=%C x).
Proof.
rewrite ltcE lecE negb_or negb_and.
case: (boolP (x == y)) => [/eqP -> | ]; first by rewrite eq_refl lerr /= !andbF.
move=> x_neqy; rewrite /= andbT.
rewrite -?real_ltrNge -?real_lerNgt ?Creal_Re ?Creal_Im ?ler_eqVlt //.
have x_rect := (Crect x); have y_rect := (Crect y).
have [ | | eq_Re] //= := (real_ltrgtP (Creal_Re x) (Creal_Re y)).
have [ | | eq_Im] //= := (real_ltrgtP (Creal_Im x) (Creal_Im y)).
by move: x_neqy; rewrite x_rect y_rect eq_Re eq_Im eq_refl.
Qed.

Lemma lecNgt x y : x <=%C y = ~~ (y <%C x).
Proof. by rewrite ltcNge negbK. Qed.

Lemma ltcc x : x <%C x = false.
Proof. by rewrite ltcE eq_refl /= andbF. Qed.

Lemma ltc_trans : transitive ltc.
Proof.
move=> y x z; rewrite ltc_neqAle => /andP [_ le_xy].
rewrite !ltcNge => /negP le_zy; apply/negP => le_zx.
by apply: le_zy; apply: (lec_trans le_zx le_xy).
Qed.

Lemma neq_ltc x y :
  (x != y) = (x <%C y) || (y <%C x).
Proof.
rewrite !ltcNge -negb_and; congr (~~ _).
apply/idP/idP => [/eqP -> | H_anti]; first by rewrite andbb.
by rewrite eq_sym; apply/eqP; apply: lec_asym.
Qed.

Lemma eqc_le x y : (x == y) = (x <=%C y && y <=%C x).
Proof. by apply/eqP/idP=> [->|/lec_asym]; rewrite ?lecc. Qed.

Lemma lec_total : total lec.
Proof. by move=> x y; rewrite lec_eqVlt ltcNge -orbA orNb orbT. Qed.

Lemma ltc_le_trans y x z : x <%C y -> y <=%C z -> x <%C z.
Proof.
by move=> lt_xy; rewrite lec_eqVlt => /orP [/eqP <- // | ]; apply: ltc_trans.
Qed.

Lemma lec_lt_trans y x z : x <=%C y -> y <%C z -> x <%C z.
Proof. by rewrite lec_eqVlt => /orP [/eqP <- // | ]; apply: ltc_trans. Qed.

Lemma ltc_eqF x y : x <%C y -> (x == y) = false.
Proof. by rewrite ltcE => /andP[ _ ] /negbTE. Qed.


(* Monotony of addition *)
Lemma lec_add2l x : {mono +%R x : y z / y <=%C z}.
Proof.
move=> y z; rewrite lecE !raddfD /= ltr_add2l ler_add2l. 
by rewrite -subr_eq0 opprD addrAC addNKr addrC subr_eq0.
Qed.

Lemma lec_add2r x : {mono +%R^~ x : y z / y <=%C z}.
Proof. by move=> y z /=; rewrite ![_ + x]addrC lec_add2l. Qed.

Lemma mono_injc f : {mono f : x y / x <=%C y} -> injective f.
Proof. by move=> mf x y /eqP; rewrite eqc_le !mf -eqc_le => /eqP. Qed.

Lemma lecW_mono f : {mono f : x y / x <=%C y} -> {mono f : x y / x <%C y}.
Proof. by move=> mf x y; rewrite !ltc_neqAle mf (inj_eq (mono_injc mf)). Qed.

Lemma lecW_mono_to (R' : eqType) (f : R -> R') (g : rel R') :
  injective f ->
  {mono f : x y / x <=%C y >-> g x y} -> 
  {mono f : x y / x <%C y >-> (x != y) && g x y}.
Proof. by move=> inj_f mf x y /=; rewrite ltc_neqAle mf (inj_eq inj_f). Qed.

Lemma ltc_add2r z x y : (x + z) <%C (y + z) = x <%C y.
Proof. by rewrite (lecW_mono (lec_add2r _)). Qed.

Lemma ltc_add2l z x y : (z + x) <%C (z + y) = x <%C y.
Proof. by rewrite (lecW_mono (lec_add2l _)). Qed.

Lemma lec_add x y z t : x <=%C y -> z <=%C t -> (x + z) <=%C (y + t).
Proof. 
by move=> lxy lzt; rewrite (@lec_trans (y + z)) ?lec_add2l ?lec_add2r. 
Qed.

Lemma ltc_add x y z t : x <%C y -> z <%C t -> (x + z) <%C (y + t).
Proof. 
by move=> lxy lzt; rewrite (@ltc_trans (y + z)) ?ltc_add2l ?ltc_add2r. 
Qed.

Lemma lec_sum (I : Type) (r : seq I) (P : pred I) (F G : I -> R) :
  (forall i : I, P i -> (F i) <=%C (G i)) -> 
  (\sum_(i <- r | P i) F i) <=%C (\sum_(i <- r | P i) G i).
Proof. by exact: (big_ind2 _ (lecc _) lec_add). Qed.

Lemma ltc_sum (I : Type) (r : seq I) (F G : I -> R) :
  (0 < size r)%N -> (forall i : I, (F i) <%C (G i)) -> 
  (\sum_(i <- r) F i) <%C (\sum_(i <- r) G i).
Proof.
case: r => [// | x r _ Hi]; rewrite big_cons big_cons.
apply: (@ltc_le_trans (G x + \sum_(j <- r) F j)); first by rewrite ltc_add2r.
by rewrite lec_add2l; apply: lec_sum => i _; rewrite lec_eqVlt Hi orbT.
Qed.

(* lec_iff *)
Definition lecif x y (C : bool) : Prop :=
    ((x <=%C y) * ((x == y) = C))%type.

Definition lec_of_leif x y C (le_xy : lecif x y C) := le_xy.1 : x <=%C y.
Coercion lec_of_leif : lecif >-> is_true.

Lemma lecifP x y C : reflect (lecif x y C) (if C then x == y else x <%C y).
Proof.
rewrite /lecif lec_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy ltc_eqF.
by move=> /orP[/eqP->|lxy] <-; rewrite ?eqxx // ltc_eqF.
Qed.

Lemma lecif_refl x C : reflect (lecif x x C) C.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.

Lemma lecif_trans x1 x2 x3 C12 C23 :
  lecif x1 x2 C12 -> lecif x2 x3 C23 -> lecif x1 x3 (C12 && C23).
Proof.
move=> ltx12 ltx23; apply/lecifP; rewrite -ltx12.
case eqx12: (x1 == x2).
  by rewrite (eqP eqx12) ltc_neqAle !ltx23 andbT; case C23.
by rewrite (@ltc_le_trans x2) ?ltx23 // ltc_neqAle eqx12 ltx12.
Qed.

Lemma lecif_le x y : x <=%C y -> lecif x y (y <=%C x).
Proof. by move=> lexy; split=> //; rewrite eqc_le lexy. Qed.

Lemma lecif_eq x y : x <=%C y -> lecif x y (x == y).
Proof. by []. Qed.

Lemma gec_lecif x y C : lecif x y C -> y <=%C x = C.
Proof. by case=> le_xy; rewrite eqc_le le_xy. Qed.

Lemma ltc_lecif x y C : lecif x y C -> (x <%C y) = ~~ C.
Proof. by move=> le_xy; rewrite ltc_neqAle !le_xy andbT. Qed.

Lemma mono_lecif (f : R -> R) C :
    {mono f : x y / x <=%C y} ->
  forall x y, (lecif (f x) (f y) C) = (lecif x y C).
Proof. by move=> mf x y; rewrite /lecif mf (inj_eq (mono_injc _)). Qed.

Lemma lecif_add x1 y1 C1 x2 y2 C2 :
    lecif x1 y1 C1 -> lecif x2 y2 C2 ->
  lecif (x1 + x2) (y1 + y2) (C1 && C2).
Proof.
rewrite -(mono_lecif _ (lec_add2r x2)) -(mono_lecif C2 (lec_add2l y1)).
exact: lecif_trans.
Qed.

Lemma lecif_sum (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> lecif (E1 i) (E2 i) (C i)) ->
  lecif (\sum_(i | P i) E1 i) (\sum_(i | P i) E2 i) [forall (i | P i), C i].
Proof.
move=> leE12; rewrite -big_andE.
elim/big_rec3: _ => [|i Ci m2 m1 /leE12]; first by rewrite /lecif lecc eqxx.
exact: lecif_add.
Qed.


(* max *)
Definition maxc x y := if (x <=%C y) then y else x.

Lemma maxcA : associative maxc.
Proof.
move=> a b c; rewrite /maxc.
case: (boolP (b <=%C c)) => [Hbc | /negbTE Hbc].
  case: (boolP (a <=%C b)) => [Hab | //].
  by rewrite Hbc (lec_trans Hab Hbc).
case: (boolP (a <=%C b)) => [Hab | ]; first by rewrite Hbc.  
rewrite -ltcNge => Hab; apply/eqP; rewrite eq_sym; apply/eqP.
apply: ifF; apply/negbTE; rewrite -ltcNge.
by apply: (ltc_trans _ Hab); rewrite ltcNge Hbc.
Qed.

Lemma maxc_addl : left_distributive +%R maxc.
Proof. by move=> x y z; rewrite /maxc /= lec_add2r; case: ifP => _. Qed.

Lemma maxc_addr : right_distributive +%R maxc.
Proof. by move=> x y z; rewrite ![x + _]addrC maxc_addl. Qed.

Lemma maxcc x : maxc x x = x.
Proof. by rewrite /maxc lecc. Qed.

Lemma maxcC : commutative maxc.
Proof.
move=> x y; rewrite /maxc; case: (boolP (x <=%C y)).
  rewrite lec_eqVlt => /orP [/eqP -> | ]; first by rewrite lecc.
  by rewrite ltcNge => /negbTE ->.
by rewrite -ltcNge ltc_neqAle => /andP[_ ->].
Qed.

Lemma maxcl x y : x <=%C (maxc x y).
Proof. by rewrite /maxc; case: (boolP (x <=%C y)). Qed.

Lemma maxcr x y : y <=%C (maxc x y).
Proof. by rewrite maxcC maxcl. Qed.

CoInductive maxc_spec x y : bool -> bool -> R -> Type :=
| Maxc_l of x <=%C y : maxc_spec x y true false y
| Maxc_r of y <%C x : maxc_spec x y false true x.

Lemma maxcP x y : maxc_spec x y (x <=%C y) (y <%C x) (maxc x y).
Proof.
case: lecP.

Print maxr_spec.
maxrP : forall (R : realDomainType) (x y : R), maxr_spec x y (y <= x) (x < y) (Num.max x y)

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

(* closed intervals instead of open ones + strict :TODO: change in polyrcf *)
Lemma deriv_sign_proper {T : rcfType} (a b : T) p :
  (forall x, x \in `]a, b[ -> p^`().[x] > 0)
  -> (forall x y, (x \in `[a, b]) && (y \in `[a, b])
    ->  x < y -> p.[x] < p.[y] ).
Proof.
move=> Pab x y; case/andP=> hx hy xy.
rewrite -subr_gte0; case: (@mvt _ x y p)=> //.
move=> c hc ->; rewrite pmulr_lgt0 ?subr_gt0 ?Pab //.
by apply: subitvP hc; rewrite //= ?(itvP hx) ?(itvP hy).
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

Section BetterParams.

Variable T : archiRcfType.

Section P_eps.

Variable x : T.
Variable p : {poly rat}.

Definition P_eps : rat :=
  if (((map_poly ratr p).[x] > 0) =P true) is (ReflectT lt_q'0)
    then sval (Q_dense_archi (lt_q'0))
    else 0.

Definition P_a : rat :=
  if (((map_poly ratr p) - (ratr P_eps)%:P != 0) =P true) 
       is ReflectT qn0
  then sval (Q_dense_archi (prev_root_lt (ltr_snaddr (ltrN10 _) (lerr x)) qn0))
  else 0.

Definition P_b : rat :=
  if (((map_poly ratr p) - (ratr P_eps)%:P != 0) =P true) 
       is ReflectT qn0
  then sval (Q_dense_archi (next_root_gt (ltr_spaddr ltr01 (lerr x)) qn0))
  else 0.

Section P_eps_cond.

Hypothesis P_lt_q'0 : (map_poly ratr p).[x] > 0.

Lemma P_lt_0e : 0 < P_eps.
Proof.
rewrite /P_eps; case: eqP => [lt_q'0| /negP]; last by rewrite P_lt_q'0.
by have /andP[] := (svalP (Q_dense_archi lt_q'0)); rewrite ltr0q.
Qed.

Lemma P_lt_eq' : ratr P_eps < (map_poly ratr p).[x].
Proof.
rewrite /P_eps; case: eqP => [lt_q'0| /negP]; last by rewrite P_lt_q'0.
by have /andP[_] := (svalP (Q_dense_archi lt_q'0)).
Qed.

Lemma P_q'e_n0 : 
  (map_poly ratr p) - (ratr P_eps)%:P != 0 :> {poly T}.
Proof.
apply/negP; move/eqP/(congr1 (fun q => q.[x]));rewrite hornerD hornerN !hornerC.
by move=> H; have := P_lt_eq'; rewrite -subr_gt0 H ltrr.
Qed.
  
Lemma P_lt_ax : ratr P_a < x.
Proof.
rewrite /P_a; case: eqP => [q_n0| /negP]; last by rewrite P_q'e_n0.
by move: (prev_root_lt _ _) => H; have /andP[_] := svalP (Q_dense_archi H).
Qed.

Lemma P_lt_xb : x < ratr P_b.
Proof.
rewrite /P_b; case: eqP => [q_n0| /negP]; last by rewrite P_q'e_n0.
by move: (next_root_gt _ _) => H; have /andP[] := svalP (Q_dense_archi H).
Qed.

Lemma P_lt_ab : P_a < P_b.
Proof. by have := (ltr_trans P_lt_ax P_lt_xb); rewrite ltr_rat. Qed.

Lemma P_lt_q' : forall y, P_a <= y <= P_b -> p.[y] > P_eps.
Proof.
move=> y /andP[le_ay le_yb].
pose q := ((map_poly ratr p) - (ratr P_eps)%:P : {poly T}).
have Heq s : q.[s] = (map_poly ratr p).[s] - ratr P_eps.
   by rewrite hornerD hornerN hornerC.
suff : Num.sg q.[ratr y] = 1.
  by move/eqP; rewrite sgr_cp0 Heq horner_map subr_gt0 ltr_rat.
have sgx : Num.sg q.[x] = 1 by apply/gtr0_sg; rewrite Heq subr_gt0 P_lt_eq'.
have nroot_x : ~~ root q x by rewrite rootE Heq subr_eq0 neqr_lt P_lt_eq' orbT.
case: (ltrgtP (ratr y) x) => [lt_yx| lt_xy | -> //].
+ rewrite (@sgr_neighplN _ _ (x - 1) _ nroot_x) ?sgx// /neighpl inE lt_yx andbT.
  apply/(@ltr_le_trans _ (ratr P_a)); last by rewrite ler_rat le_ay.
  rewrite /P_a; case: eqP => [q_n0| /negP]; last by rewrite P_q'e_n0.
  by move: (prev_root_lt _ _) => H; have /andP[] := svalP (Q_dense_archi H).
rewrite rootE in nroot_x.
rewrite (@sgr_neighprN _ _ _ (x + 1) nroot_x) ?sgx// /neighpr inE lt_xy /=. 
apply/(@ler_lt_trans _ (ratr P_b)); first by rewrite ler_rat le_yb.
rewrite /P_b; case: eqP => [q_n0| /negP]; last by rewrite P_q'e_n0.
by move: (next_root_gt _ _) => H; have /andP[] := svalP (Q_dense_archi H).
Qed.

Lemma P_int_lt0 {fT : rcfType} (y : fT) :
  y \in `](ratr P_a), (ratr P_b)[ -> 0 < (map_poly ratr p).[y].
Proof.
rewrite inE /= => /andP[lt_ay lt_yb].
by apply/(map_poly_pos P_lt_0e P_lt_q'); rewrite (ltrW lt_ay) (ltrW lt_yb).
Qed.

End P_eps_cond.

End P_eps.

Section BP_Defs.

Variable x : T.
Variable p : {poly rat}.

(* Lemma P_int_neq0 {fT : rcfType} (y : fT) : *)
(*   (map_poly ratr p).[x] != 0 ->  *)
(*   y \in `](ratr (P_a x p)), (ratr (P_b x p))[ -> *)
(*   y \in `](ratr (P_a x (-p))), (ratr (P_b x (-p)))[ ->               *)
(*   (map_poly ratr p).[y] != 0. *)
(* Proof. *)
(* move=> H; case: (boolP ((map_poly ratr p).[x] > 0)) => [H1 H2 | ]. *)
(*   by have /gtr_eqF -> := P_int_lt0 H1 H2. *)
(* rewrite -lerNgt ler_eqVlt (negbTE H) orFb -lter_oppE oppr0 -hornerN -rmorphN /=. *)
(* move/(P_int_lt0)/(_ fT y); rewrite rmorphN hornerN lter_oppE /= neqr_lt. *)
(* by move => H1 _ H3; rewrite (H1 H3). *)
(* Qed. *)

Section Def.

Definition BP_poly : {poly rat} :=
  if ((p != 0) && (root (map_poly ratr p) x))
    then let q := p %/ (gcdp p p^`()) in
         if ((map_poly ratr q)^`().[x] > 0)
           then q
           else -q
    else 0.

Definition BP_eps := P_eps x BP_poly^`().
Definition BP_a := P_a x BP_poly^`().
Definition BP_b := P_b x BP_poly^`().

End Def.

Section Lemmas.

Hypothesis pn0 : p != 0.
Hypothesis root_p : root (map_poly ratr p) x.

Lemma BP_poly_neq0 : BP_poly != 0.
Proof.
rewrite /BP_poly pn0 root_p /=.
have H : p %/ gcdp p p^`() != 0 by rewrite dvdp_div_eq0 ?dvdp_gcdl ?p_neq0.
by case: ifP => _ //; rewrite oppr_eq0.
Qed.

Lemma BP_separable : separable.separable_poly BP_poly.
Proof.
rewrite /BP_poly pn0 root_p /=; case: ifP => _.
  by apply/separable.make_separable/pn0.
have : (- (p %/ gcdp p p^`()) %| p %/ gcdp p p^`()) by rewrite -dvdp_opp dvdpp.
by move/separable.dvdp_separable; apply; apply/separable.make_separable/pn0.
Qed.

(* :TODO: even longer than before (cf other dev or better_params) *)
Lemma BP_root {fT : realFieldType} (y : fT) : 
  root (map_poly ratr p) y = root (map_poly ratr BP_poly) y.
Proof.
apply/idP/idP; last first.
  rewrite /BP_poly pn0 root_p /= => H1.
  have H : root (map_poly ratr (p %/ gcdp p p^`())) y.
    by move: H1; case: ifP => _ //; rewrite rmorphN rootN /=.
  by rewrite -(divpK (dvdp_gcdl p p^`())) rmorphM /= rootM H.
move=> rooty; rewrite /BP_poly pn0 root_p /=.
suff H : root (map_poly ratr (p %/ gcdp p p^`())) y.
  by case: ifP => _ //; rewrite rmorphN rootN /=.
rewrite map_divp gcdp_map -deriv_map /= -mu_gt0; set q := gcdp _ _; last first.
  by rewrite (dvdp_div_eq0 (dvdp_gcdl _ _)) map_poly_eq0 pn0.
have H : ((map_poly ratr p) != 0 :> {poly fT}) by rewrite map_poly_eq0 pn0.
have := H; rewrite -[X in X != 0](divpK (dvdp_gcdl _ (map_poly ratr p)^`())).
move/(mu_mul y); rewrite (divpK (dvdp_gcdl _ _)) mu_gcdp; last first.
  apply/mulf_neq0; first by rewrite map_poly_eq0 pn0.
  rewrite -size_poly_eq0 -lt0n size_deriv /= -subn1 subn_gt0.
  by apply/(root_size_gt1 _ rooty); rewrite map_poly_eq0 pn0.
move/eqP; rewrite -/q (mu_deriv_root H rooty) -[X in minn _ X]addn0. 
by rewrite -addn_minr minn0 addn0 addnC eqn_add2r eq_sym => /eqP ->.
Qed. 

Lemma BP_rootx : root (map_poly ratr BP_poly) x.
Proof. by rewrite -BP_root root_p. Qed.

Lemma BP_lt_q'0 : (map_poly ratr BP_poly^`()).[x] > 0.
Proof.
have:= BP_rootx; rewrite -deriv_map /BP_poly pn0 root_p; case: ifP=> //= /negbT.
rewrite -lerNgt ler_eqVlt => /orP[]; last first.
  by rewrite rmorphN derivN hornerN ltr_oppr oppr0.
rewrite -rootE deriv_map /= rmorphN rootN /=; set q := _ %/ _ => root_q' root_q.
have : map_poly ratr p != 0 :> {poly T} by rewrite map_poly_eq0.
move/separable.make_separable; rewrite /separable.separable_poly -/q.
rewrite deriv_map -gcdp_map -map_divp /= -/q => /coprimep_root /(_ root_q).
by rewrite -rootE deriv_map root_q'.
Qed.

Lemma BP_lt_ax : ratr BP_a < x.
Proof. exact: (P_lt_ax BP_lt_q'0). Qed.

Lemma BP_lt_xb : x < ratr BP_b.
Proof. exact: (P_lt_xb BP_lt_q'0). Qed.

Lemma BP_int_deriv {fT : rcfType} (y : fT) :
  y \in `](ratr BP_a), (ratr BP_b)[ -> 0 < (map_poly ratr BP_poly)^`().[y].
Proof. by rewrite deriv_map; apply: (P_int_lt0 BP_lt_q'0). Qed.

Lemma BP_ltx_p0 y : ratr BP_a <= y -> y < x -> (map_poly ratr BP_poly).[y] < 0.
Proof.
move=> le_ay lt_yx; have /deriv_sign_proper/(_ _ _ _ lt_yx) :=(@BP_int_deriv T).
have /rootP -> := BP_rootx; rewrite !inE le_ay (ltrW BP_lt_ax) (ltrW BP_lt_xb).
by apply; rewrite !andbT /=; apply/ltrW/(ltr_trans lt_yx BP_lt_xb).
Qed.

Lemma BP_lt_pa0 : BP_poly.[BP_a] < 0.
Proof. by have := (BP_ltx_p0 (lerr _) BP_lt_ax); rewrite horner_map ltrq0. Qed.

Lemma BP_ltx_0p y : y <= ratr BP_b -> x < y -> 0 < (map_poly ratr BP_poly).[y].
Proof.
move=> le_yb lt_xy; have /deriv_sign_proper/(_ _ _ _ lt_xy):=(@BP_int_deriv T).
have /rootP -> := BP_rootx; rewrite !inE le_yb (ltrW BP_lt_ax) (ltrW BP_lt_xb).
by apply; rewrite !andbT /=; apply/ltrW/(ltr_trans BP_lt_ax lt_xy). 
Qed.

Lemma BP_lt_0pb : 0 < BP_poly.[BP_b].
Proof. by have := (BP_ltx_0p (lerr _) BP_lt_xb); rewrite horner_map ltr0q. Qed.

Lemma BP_int_p0 {fT : rcfType} : 
  (0 : fT) \in `](map_poly ratr BP_poly).[ratr BP_a], 
                    (map_poly ratr BP_poly).[ratr BP_b][.
Proof. by rewrite inE !horner_map ltrq0 ltr0q BP_lt_pa0 BP_lt_0pb. Qed.

Lemma BP_lt_ab_fT {fT : rcfType} : ratr BP_a < ratr BP_b :> fT.
Proof. by rewrite ltr_rat (P_lt_ab BP_lt_q'0). Qed.

Lemma BP_xroots :
  roots (map_poly ratr BP_poly) (ratr BP_a) (ratr BP_b) = [:: x].
Proof.
apply/esym/roots_uniq; rewrite ?map_poly_eq0 ?BP_poly_neq0 // /roots_on =>y.
rewrite !inE; case: (boolP (y > ratr BP_a)) => [lt_ay | ] /=; last first.
  by rewrite -lerNgt; move=> H; apply/esym/ltr_eqF/(ler_lt_trans H)/BP_lt_ax.
case: (boolP (y < ratr BP_b)) => [lt_yb | ] /=; last first.
  by rewrite -lerNgt; move=> H; apply/esym/gtr_eqF/(ltr_le_trans _ H)/BP_lt_xb.
case: (ltrgtP y x) => [lt_yx | lt_xy | ->]; last by rewrite -BP_root.
  by rewrite rootE; apply/ltr_eqF/(BP_ltx_p0 _ lt_yx)/ltrW/lt_ay.
by rewrite rootE; apply/gtr_eqF/(BP_ltx_0p _ lt_xy)/ltrW/lt_yb.
Qed.

End Lemmas.

Variable fT : rcfType.

Section BP_valDef.

Definition BP_val : fT :=
  if ((p != 0) =P true, (root (map_poly ratr p) x) =P true)
       is (ReflectT pn0, ReflectT rootp)
  then sval (derp_root (BP_int_deriv pn0 rootp) 
                       (ltrW (BP_lt_ab_fT pn0 rootp)) (BP_int_p0 pn0 rootp))
  else 0.

End BP_valDef.

Section BP_valLemmas.

Hypothesis pn0 : p != 0.
Hypothesis rootp : root (map_poly ratr p) x.

Lemma BP_lt_av : ratr BP_a < BP_val.
Proof.
rewrite /BP_val; case: eqP; last by rewrite pn0. 
case: eqP; last by rewrite rootp.
by move=> p0 pr; move: (derp_root _ _ _) => H; have [_ _ /andP[]]:= svalP H.
Qed.

Lemma BP_lt_vb : BP_val < ratr BP_b.
Proof.
rewrite /BP_val; case: eqP; last by rewrite pn0. 
case: eqP; last by rewrite rootp.
by move=> p0 pr; move: (derp_root _ _ _) => H; have [_ _ /andP[]]:= svalP H.
Qed.

Lemma BP_rootv : root (map_poly ratr BP_poly) BP_val.
Proof.
rewrite /BP_val; case: eqP; last by rewrite pn0. 
case: eqP; last by rewrite rootp.
by move=> p0 pr; move: (derp_root _ _ _) => H; have [_ /rootP ->] := svalP H.
Qed.

Lemma BP_ltv_p0 y : 
  ratr BP_a <= y -> y < BP_val -> (map_poly ratr BP_poly).[y] < 0.
Proof.
move=> le_ay; rewrite /BP_val; case: eqP; last by rewrite pn0.
case: eqP; last by rewrite rootp.
move=> p0 pr; move: (derp_root _ _ _) => H lt_yv.
by have [H1 _ _ _] := svalP H; have := (H1 y); rewrite inE lt_yv le_ay; apply.
Qed.

Lemma BP_ltv_0p y : 
  y <= ratr BP_b -> BP_val < y -> 0 < (map_poly ratr BP_poly).[y].
Proof.
move=> le_yb; rewrite /BP_val; case: eqP; last by rewrite pn0.
case: eqP; last by rewrite rootp.
move=> p0 pr; move: (derp_root _ _ _) => H lt_vy.
by have [_ _ _] := svalP H; move/(_ y); rewrite inE lt_vy le_yb; apply.
Qed.

Lemma BP_lt_inf (q : rat) : (ratr q < BP_val) = (ratr q < x).
Proof.
case: (boolP (q < BP_a)) => [lt_qa | ].
  apply/idP/idP => _.
    by apply/(ltr_trans _ (BP_lt_ax _ _)); rewrite // ltr_rat lt_qa.
  by apply/(ltr_trans _ BP_lt_av); rewrite ltr_rat lt_qa.
rewrite -lerNgt => le_aq; apply/idP/idP => [lt_qv | lt_qx].
  have := (ltr_trans lt_qv BP_lt_vb); rewrite ltr_rat -(ltr_rat T) => lt_qb.
  have := le_aq; rewrite -(ler_rat fT) => /BP_ltv_p0 /(_ lt_qv) BPq_lt0.
  case: (ltrgtP) => [lt_xq|//|eq_xq].
    have := BP_ltx_0p pn0 rootp (ltrW lt_qb) lt_xq; rewrite ltrNge. 
    by have := (ltrW BPq_lt0); rewrite !horner_map !lerq0 => ->.
  have := (BP_rootx pn0 rootp); rewrite rootE eq_xq.
  by have := (ltr_eqF BPq_lt0); rewrite !horner_map !fmorph_eq0 => ->.
have := (ltr_trans lt_qx (BP_lt_xb pn0 rootp)); rewrite ltr_rat -(ltr_rat fT).
move=> lt_qb; have := le_aq; rewrite -(ler_rat T) => /(BP_ltx_p0 pn0 rootp).
move=> /(_ lt_qx) BPq_lt0; case: (ltrgtP) => [lt_vq|//|eq_vq].
  have := BP_ltv_0p (ltrW lt_qb) lt_vq; rewrite ltrNge.
  by have := (ltrW BPq_lt0); rewrite !horner_map !lerq0 => ->.
have := BP_rootv; rewrite rootE eq_vq.
by have /ltr_eqF := BPq_lt0; rewrite !horner_map !fmorph_eq0 => ->.
Qed.

Lemma BP_lt_sup (q : rat) : (BP_val < ratr q) = (x < ratr q).
Proof.
case: (boolP (q > BP_b)) => [lt_bq | ].
  apply/idP/idP => _.
    by apply/(ltr_trans (BP_lt_xb _ _)); rewrite // ltr_rat lt_bq.
  by apply/(ltr_trans BP_lt_vb); rewrite ltr_rat lt_bq.
rewrite -lerNgt => le_qb; apply/idP/idP => [lt_vq | lt_xq].
  have := (ltr_trans BP_lt_av lt_vq); rewrite ltr_rat -(ltr_rat T) => lt_aq.
  have := le_qb; rewrite -(ler_rat fT) => /BP_ltv_0p /(_ lt_vq) BPq_lt0.
  case: (ltrgtP) => [lt_qx|//|eq_qx].
    have := BP_ltx_p0 pn0 rootp (ltrW lt_aq) lt_qx; rewrite ltrNge.
    by have := (ltrW BPq_lt0); rewrite !horner_map !ler0q => ->.
  have := (BP_rootx pn0 rootp); rewrite rootE -eq_qx.
  by have := (gtr_eqF BPq_lt0); rewrite !horner_map !fmorph_eq0 => ->.
have := (ltr_trans (BP_lt_ax pn0 rootp) lt_xq); rewrite ltr_rat -(ltr_rat fT).
move=> lt_aq; have := le_qb; rewrite -(ler_rat T) => /(BP_ltx_0p pn0 rootp).
move=> /(_ lt_xq) BPq_lt0; case: (ltrgtP) => [lt_qv|//|eq_qv].
  have := BP_ltv_p0 (ltrW lt_aq) lt_qv; rewrite ltrNge.
  by have := (ltrW BPq_lt0); rewrite !horner_map !ler0q => ->. 
have := BP_rootv; rewrite rootE -eq_qv.
by have /gtr_eqF := BPq_lt0; rewrite !horner_map !fmorph_eq0 => ->.
Qed.

Lemma BP_val_eq (y : fT) : 
  (BP_val == y) = 
  ((ratr BP_a < y < ratr BP_b) && root (map_poly ratr BP_poly) y).
Proof.
apply/eqP/andP => [<- | [/andP[]]]; first by rewrite BP_lt_av BP_lt_vb BP_rootv.
move=> lt_ay lt_yb rooty.
have y_in : y \in `](ratr BP_a), (ratr BP_b)[ by rewrite inE lt_ay lt_yb.
have []:= (@monotonic_rootN fT (map_poly ratr BP_poly) (ratr BP_a) (ratr BP_b)).
+ move=> z /(BP_int_deriv pn0 rootp); rewrite rootE neqr_lt => ->.
  by rewrite orbT.
+ by move/roots_on_nil/(_ y y_in); rewrite rooty.
move=> [z /roots_onP H]; have := (H y y_in); rewrite rooty /= inE => /esym /eqP.
have : BP_val \in `](ratr BP_a), (ratr BP_b)[ by rewrite inE BP_lt_av BP_lt_vb.
by move/H; rewrite BP_rootv /= inE; move/esym/eqP => -> ->.
Qed.

Lemma BP_vroots :
  roots (map_poly ratr BP_poly) (ratr BP_a) (ratr BP_b) = [:: BP_val].
Proof.
apply/esym/roots_uniq; rewrite ?map_poly_eq0 ?BP_poly_neq0 //.
by rewrite /roots_on => y; rewrite !inE eq_sym BP_val_eq.
Qed.

Lemma BP_valP (y : fT) :
  reflect ((forall qa qb : rat, (ratr qa < x < ratr qb) -> 
                                (ratr qa < y < ratr qb)) /\
           (root (map_poly ratr p) y)) 
          (BP_val == y).
Proof.
apply (iffP idP) => [/eqP H | ]. 
  split; rewrite -H ; first by move=> qa qb; rewrite ?BP_lt_inf ?BP_lt_sup.
  by rewrite BP_root ?BP_rootv.
move=> [Hint Hroot]; rewrite BP_val_eq Hint -?BP_root ?Hroot //.
by rewrite -BP_lt_inf -BP_lt_sup BP_lt_av BP_lt_vb.
Qed.

End BP_valLemmas.

End BP_Defs.

Section BP_morph.

Variable fT : rcfType.

Lemma BP_val_root (x : T) (p q : {poly rat}) :
  p != 0 -> root (map_poly ratr p) x ->
  q != 0 -> root (map_poly ratr q) x -> 
  root (map_poly ratr q) (BP_val x p fT).
Proof.
move=> pn0 rootpx qn0 rootqx; set v := BP_val _ _ _.
pose r := (gcdp (BP_poly x p) q).
have rootr : root (map_poly ratr r) x.
  by rewrite gcdp_map root_gcd /= rootqx -BP_root ?rootpx ?pn0.
suff : root (map_poly ratr r) v by rewrite gcdp_map root_gcd /= => /andP[].
have := (divpK (dvdp_gcdl (BP_poly x p) q)); rewrite -/r => eq_BP.
have := BP_vroots fT pn0 rootpx; rewrite -eq_BP rmorphM mulrC /= => Hm.
have := BP_separable pn0 rootpx; rewrite -eq_BP separable.separable_mul.
move=> /andP[BPr_sep /andP[r_sep]]; rewrite coprimep_sym => BPr_cop.
have x_n0 : (map_poly ratr ((BP_poly x p) %/ r)).[x] != 0.
  by apply/(coprimep_root _ rootr); rewrite coprimep_map BPr_cop.
have rn0 : (map_poly ratr r) != 0 :> {poly fT}.
  by rewrite map_poly_eq0 gcdp_eq0 negb_and qn0 orbT.
have brn0 : (map_poly ratr ((BP_poly x p) %/ r)) != 0 :> {poly fT}.
  rewrite map_poly_eq0; apply/negP=> /eqP H.
  by have := x_n0; rewrite H rmorph0 horner0 eq_refl.
have := BPr_cop; rewrite -(coprimep_map (@ratr_rmorphism fT)).
move/(roots_mul_coprime (BP_lt_ab_fT pn0 rootpx) rn0 brn0); rewrite Hm => Hmm.
suff /negbTE H : ~~ root (map_poly ratr ((BP_poly x p) %/ r)) v.
  have : v \in [:: v] by rewrite inE.
  rewrite (perm_eq_mem Hmm) mem_cat. 
  by rewrite -!root_is_roots ?H ?orbF ?inE ?BP_lt_av ?BP_lt_vb.
have := x_n0; rewrite rootE !neqr_lt => /orP[| H]; last first.
  have/P_int_lt0 -> := H; rewrite ?orbT // inE ?BP_lt_inf ?BP_lt_sup //.
  by rewrite ?P_lt_ax ?P_lt_xb.
rewrite -[_ < 0]lter_oppE -[_ < 0]lter_oppE -!hornerN -!rmorphN /= => H.
have/P_int_lt0 -> := H; rewrite //= inE ?BP_lt_inf ?BP_lt_sup //.
by rewrite ?P_lt_ax ?P_lt_xb.
Qed.


Lemma BP_valpP (x : T) (y : fT) (p q : {poly rat}) :
  p != 0 -> root (map_poly ratr p) x ->
  q != 0 -> root (map_poly ratr q) x ->
  reflect ((forall qa qb : rat, (ratr qa < x < ratr qb) -> 
                                (ratr qa < y < ratr qb)) /\
           (root (map_poly ratr q) y)) 
          (BP_val x p fT == y).
Proof.
move=> pn0 rootpx qn0 rootqx.
apply (iffP idP) => [Heq |[]].
  split; first by have /(BP_valP pn0 rootpx) [] := Heq.
  by have /eqP <- := Heq; apply: BP_val_root.
move=> Hrat rootqy.
have rootbx : root (map_poly ratr (BP_poly x q)) x by rewrite -BP_root.
have rootby : root (map_poly ratr (BP_poly x q)) y by rewrite -BP_root.
have rootbv : root (map_poly ratr (BP_poly x q)) (BP_val x p fT).
  by apply/BP_val_root/rootbx/BP_poly_neq0/rootqx/qn0.
have v_in : (BP_val x p fT) \in `](ratr (BP_a x q)), (ratr (BP_b x q))[.
  by rewrite inE ?BP_lt_sup ?BP_lt_inf // ?BP_lt_ax ?BP_lt_xb.
have []:= (@monotonic_rootN fT (map_poly ratr (BP_poly x q)) 
                            (ratr (BP_a x q)) (ratr (BP_b x q))).
+ move=> z /(BP_int_deriv qn0 rootqx); rewrite rootE neqr_lt => ->.
  by rewrite orbT.
+ by move/roots_on_nil/(_ (BP_val x p fT) v_in); rewrite rootbv.
move=> [z /roots_onP H]; have :=(H _ v_in); rewrite rootbv /= inE => /esym /eqP.
have : y \in `](ratr (BP_a x q)), (ratr (BP_b x q))[. 
  by rewrite inE Hrat ?BP_lt_ax ?BP_lt_xb.
by move/H; rewrite rootby /= inE; move/esym/eqP => -> ->.
Qed.

Variables x y : T.
Variables p q r : {poly rat}.

Hypothesis pn0 : p != 0.
Hypothesis qn0 : q != 0.
Hypothesis rn0 : r != 0.
Hypothesis rootpx : root (map_poly ratr p) x.
Hypothesis rootqy : root (map_poly ratr q) y.

Lemma BP_val0 (s : {poly rat}) (sn0 : s != 0) 
      (roots0 : root (map_poly ratr s) (0 : T)) : 
  BP_val 0 s fT = 0.
Proof.
apply/eqP/(BP_valP sn0 roots0); have fT0 := (rmorph0 _ : ratr 0 = 0 :> fT).
have T0 := (rmorph0 _ : ratr 0 = 0 :> T); split; last first.
  by have := roots0; rewrite !rootE -fT0 -T0 !horner_map fT0 T0 /= !fmorph_eq0.
by move=> qa qb; rewrite -fT0 -T0 !ltr_rat.
Qed.

Lemma BP_val1 (rootr1 : root (map_poly ratr r) (1 : T)) : 
  BP_val 1 r fT = 1.
Proof.
apply/eqP/(BP_valP rn0 rootr1); have fT1 := (rmorph1 _ : ratr 1 = 1 :> fT).
have T1 := (rmorph1 _ : ratr 1 = 1 :> T); split; last first.
  by have := rootr1; rewrite !rootE -fT1 -T1 !horner_map /= !fmorph_eq0.
by move=> qa qb; rewrite -fT1 -T1 !ltr_rat.
Qed.

Lemma BP_valB (rootrxy : root (map_poly ratr r) (x - y)) :
  (BP_val (x - y) r fT) = (BP_val x p fT) - (BP_val y q fT).
Proof.
pose pm := (lead_coef p)^-1 *: p.
have pmn0 : pm != 0.
  by rewrite /pm scale_poly_eq0 negb_or invr_eq0 lead_coef_eq0 pn0.
have rootpmx : root (map_poly ratr pm) x.
  by rewrite /pm map_polyZ /= rootZ // fmorph_eq0 invr_eq0 lead_coef_eq0 pn0.
have /eqP -> : BP_val x p fT == BP_val x pm fT.
  apply/BP_valP => //; split; last by rewrite BP_val_root.
  by move=> qa qb Hrat; rewrite BP_lt_inf ?BP_lt_sup.
pose P := polyXY.sub_annihilant pm q.
have Pn0 : P != 0 by apply: polyXY.sub_annihilant_neq0.
have rootPxy : root (map_poly ratr P) (x - y).
  by apply/rootP/polyXY.map_sub_annihilantP => //; apply/rootP.
apply/eqP/(BP_valpP _ _ _ Pn0 rootPxy) => //; split; last first.
  by apply/rootP/polyXY.map_sub_annihilantP => //=; apply/rootP/BP_val_root.
move=> qa qb /andP[lt_qaxy lt_xyqb].
pose e := Num.min ((x - y) - ratr qa) (ratr qb - (x - y)).
have e_gt0 : e / 2%:R > 0. 
  by rewrite divr_gt0 ?ltr0n // ltr_minr !subr_gt0 lt_qaxy lt_xyqb. 
have [qe /andP[lt_0qe]] := Q_dense_archi e_gt0.
rewrite ltr_pdivl_mulr ?ltr0n // mulr_natr mulr2n => lt_qeqee.
have /Q_dense_archi [qx /andP[]] : x - ratr qe < x.
  by rewrite ltr_subl_addr ltr_addl lt_0qe. 
rewrite ltr_subl_addr -rmorphD /= => lt_xq lt_qx.
have /Q_dense_archi [qy /andP[]] : y - ratr qe < y.
  by rewrite ltr_subl_addr ltr_addl lt_0qe. 
rewrite ltr_subl_addr -rmorphD /= => lt_yq lt_qy.
have lt_qa : ratr qa < ratr qx - ratr (qy + qe) :> fT.
  rewrite -rmorphB ltr_rat -(ltr_rat T).
  apply/(@ler_lt_trans _ ((x - y) - e)). 
    by rewrite ler_subr_addr -ler_subr_addl ler_minl lerr.
  rewrite addrAC opprD addrA [in ratr _]addrAC rmorphB /=.
  apply/(ltr_sub _ lt_qy); rewrite ltr_subl_addr -ltr_subl_addl.
  apply/(ltr_trans _ lt_qeqee); rewrite rmorphB opprB /=.
  by rewrite addrA ltr_subl_addl addrA ltr_add2r -rmorphD.
have lt_qb : ratr (qx + qe) - ratr qy < ratr qb :> fT.
  rewrite -rmorphB ltr_rat -(ltr_rat T).
  apply/(@ltr_le_trans _ ((x - y) + e)); last first. 
    by rewrite -ler_subr_addl ler_minl lerr orbT.
  rewrite -[in ratr _]addrA rmorphD rmorphB /= -addrA; apply/(ltr_add lt_qx).
  rewrite [-y + e]addrC ltr_subr_addl; apply/(ltr_trans _ lt_qeqee).
  by rewrite addrA ltr_subl_addl addrA ltr_add2r -rmorphD lt_yq.
apply/andP; split.
  by apply/(ltr_trans lt_qa)/ltr_sub; rewrite ?BP_lt_sup ?BP_lt_inf.
by apply/(ltr_trans _ lt_qb)/ltr_sub; rewrite ?BP_lt_sup ?BP_lt_inf //.
Qed.

Lemma BP_valM (rootrxy : root (map_poly ratr r) (x * y)) :
  (BP_val (x * y) r fT) = (BP_val x p fT) * (BP_val y q fT).
Proof.
case: (boolP (y == 0)) => [/eqP eq_y0 | y_neq0].
  rewrite eq_y0 mulr0 !BP_val0 ?mulr0 //; last by rewrite -eq_y0 rootqy.
  by have := rootrxy; rewrite eq_y0 mulr0.
have yvn0 : BP_val y q fT != 0.
  rewrite neqr_lt -(rmorph0 _ : ratr 0 = 0) ?BP_lt_inf ?BP_lt_sup //.
  by rewrite !rmorph0 -neqr_lt.
apply/(divIf yvn0)/esym; rewrite (mulfK yvn0) -[x in LHS](mulfK y_neq0).
move: q qn0 rootqy yvn0 => q' q'n0 rootq'y yvn0.
wlog: q' q'n0 rootq'y yvn0 / q'.[0] != 0.
  move=> H; pose s := gdcop 'X q'.
  have sn0 : s != 0 by rewrite /s cauchyreals.gdcop_eq0 negb_and q'n0.
  have rootsy : root (map_poly ratr s) y.
    by rewrite gdcop_map /= root_gdco ?map_poly_eq0 // rootq'y map_polyX rootX.
  have yvsn0 : BP_val y s fT != 0.
    rewrite neqr_lt -(rmorph0 _ : ratr 0 = 0) ?BP_lt_inf ?BP_lt_sup //.
    by rewrite !rmorph0 -neqr_lt.
  have nroots0 : s.[0] != 0.
    by rewrite -rootE root_gdco ?q'n0 // rootX eq_refl /= andbF.
  have -> := H s sn0 rootsy yvsn0 nroots0; congr (_ / _); apply/eqP.
  rewrite BP_val_eq // ?BP_lt_inf ?BP_lt_sup // ?BP_lt_ax ?BP_lt_xb //=.
  by apply/(BP_val_root q'n0 rootq'y (BP_poly_neq0 sn0 rootsy))/BP_rootx.
move=> q'0n0; pose P := polyXY.div_annihilant r q'.
have Pn0 : P != 0 by apply: polyXY.div_annihilant_neq0.
have rootPxy : root (map_poly ratr P) ((x * y) / y).
  by apply/rootP/polyXY.map_div_annihilantP => //; apply/rootP.
have rootpxy : root (map_poly ratr p) ((x * y) / y).
  by rewrite mulfK ?rootpx ?y_neq0.
apply/eqP; apply/ (BP_valpP _ pn0 rootpxy Pn0 rootPxy) => //; split; last first.
  by apply/rootP/polyXY.map_div_annihilantP => //=; apply/rootP/BP_val_root.
move: x rootrxy => x'; move: y y_neq0 rootq'y => y' y'_neq0 rootq'y rootrxy.
set xb := BP_val _ _ _; set yb := BP_val _ _ _.
have BP_gt_0 z Q (Qn0 : Q != 0) (rootQz : root (map_poly ratr Q) z) :
                   (z > 0) = ((BP_val z Q fT) > 0). 
  by rewrite -(rmorph0 _ : ratr 0 = 0 :> fT) BP_lt_inf ?rmorph0.
have BP_lt_0 z Q (Qn0 : Q != 0) (rootQz : root (map_poly ratr Q) z) :
                   (z < 0) = ((BP_val z Q fT) < 0). 
  by rewrite -(rmorph0 _ : ratr 0 = 0 :> fT) BP_lt_sup ?rmorph0.
suff Hnorm1 : forall qa qb : rat, 0 <= qa -> ratr qa < `|x' * y' / y'| < ratr qb ->
    ratr qa < `| xb / yb|  < ratr qb.
  move=> qa qb /andP[lt_qaxy lt_xyqb].
  case: (ltrgtP (x' * y' / y' ) 0) => [lt_x'y'0| lt_0x'y'| eq_x'y'0].
  + have -> : xb / yb = - `| xb / yb |.
      rewrite ltr0_norm ?opprK //.
      have := y'_neq0; rewrite neqr_lt => /orP[lt_y'0 | lt_0y'].
        rewrite ltr_ndivr_mulr ?mul0r -?BP_gt_0 -?BP_lt_0 //.
        by have := lt_x'y'0; rewrite (ltr_ndivr_mulr _ _ lt_y'0) mul0r.
      rewrite ltr_pdivr_mulr ?mul0r -?BP_gt_0 -?BP_lt_0 //.
      by have := lt_x'y'0; rewrite (ltr_pdivr_mulr _ _ lt_0y') mul0r.
    rewrite ltr_oppr ltr_oppl andbC -!rmorphN /=.
    suff : ratr (Num.max (-qb) 0) < `|xb / yb| < ratr (-qa). 
      move=> /andP[]; move/(ler_lt_trans _) => ->; rewrite ?andTb // ler_rat.
      by rewrite ler_maxr lerr.
    apply: Hnorm1; first by rewrite ler_maxr lerr orbT.
    rewrite (ltr0_norm lt_x'y'0) rmorphN lter_oppE /= lt_qaxy andbT ltr_oppr.
    case: maxrP => _; first by rewrite rmorphN opprK /= lt_xyqb.
    by rewrite rmorph0 oppr0 lt_x'y'0. 
  + have -> : xb / yb = `| xb / yb |.
      rewrite gtr0_norm //.
      have := y'_neq0; rewrite neqr_lt => /orP[lt_y'0 | lt_0y'].
        rewrite ltr_ndivl_mulr ?mul0r -?BP_gt_0 -?BP_lt_0 //.
        by have := lt_0x'y'; rewrite (ltr_ndivl_mulr _ _ lt_y'0) mul0r.
      rewrite ltr_pdivl_mulr ?mul0r -?BP_gt_0 -?BP_lt_0 //.
      by have := lt_0x'y'; rewrite (ltr_pdivl_mulr _ _ lt_0y') mul0r.
    suff : ratr (Num.max qa 0) < `|xb / yb | < ratr qb.
      move=> /andP[]; move/(ler_lt_trans _) => ->; rewrite ?andTb // ler_rat.
      by rewrite ler_maxr lerr.
    apply/Hnorm1; first by rewrite ler_maxr lerr orbT.
    rewrite (gtr0_norm lt_0x'y'); case: maxrP => _; first by rewrite /= lt_qaxy.
    by rewrite rmorph0 lt_0x'y' lt_xyqb.
  have /eqP eq_x'0 : x' == 0.
    by have /eqP := eq_x'y'0; rewrite !mulf_eq0 invr_eq0 (negbTE y'_neq0) !orbF.
  rewrite /xb eq_x'0 mul0r BP_val0 // ?mul0r ?ltr0q ?ltrq0.
    have := lt_qaxy; have := lt_xyqb.
    by rewrite eq_x'0 !mul0r ltr0q ltrq0 => -> ->.
  by have := rootrxy; rewrite eq_x'0 mul0r.
move=> qa; wlog: qa / 0 < qa => [ihp qb| lt_0a].
  rewrite ler_eqVlt => /orP[/eqP/esym ->| lt_0qa]; last first.
    by apply: ihp => //; apply/ltrW.
  rewrite !rmorph0 => /andP[lt_0n lt_nb].
  have [qa' /andP[lt_0a' lt_a'n]] := Q_dense_archi lt_0n.
  suff: ratr qa' < `|xb / yb| < ratr qb.
    move=> /andP[lt_q'n ->]; rewrite andbT.
    by apply/(ltr_trans _ lt_q'n); have := lt_0a'; rewrite !ltr0q.
  apply/ihp; rewrite ?lt_a'n ?lt_nb //; have := lt_0a'; rewrite ltr0q //.
  by apply/ltrW.
have BP_infn z Q (Qn0 : Q != 0) (rootQ : root (map_poly ratr Q) z) u :
  (ratr u < `|z|) = (ratr u < `|BP_val z Q fT|).
  case: ltrgt0P; last by move=> Heq; rewrite Heq BP_val0 ?normr0 ?ltrq0 // -Heq.
    by rewrite (BP_gt_0 _ _ Qn0 rootQ) => /gtr0_norm ->; rewrite BP_lt_inf.
  rewrite (BP_lt_0 _ _ Qn0 rootQ) => /ltr0_norm ->.
  by rewrite ltr_oppr -rmorphN BP_lt_sup ?rmorphN //= ltr_oppr.
have BP_supn z Q (Qn0 : Q != 0) (rootQ : root (map_poly ratr Q) z) u :
  (`|z| < ratr u) = (`|BP_val z Q fT| < ratr u).
  case: ltrgt0P; last by move=> Heq; rewrite Heq BP_val0 ?normr0 ?ltr0q // -Heq.
    by rewrite (BP_gt_0 _ _ Qn0 rootQ) => /gtr0_norm ->; rewrite BP_lt_sup.
  rewrite (BP_lt_0 _ _ Qn0 rootQ) => /ltr0_norm ->.
  by rewrite ltr_oppl -rmorphN BP_lt_inf ?rmorphN //= ltr_oppl.
move=> qb _ {BP_gt_0 BP_lt_0 yvn0 q'0n0 P Pn0 rootPxy rootpxy}.
rewrite normrM [`|xb / yb|]normrM !normfV => /andP[lt_axy lt_xyb].
have lt_0y: 0 < `|y'| by rewrite normr_gt0.
have lt_0xy: 0 < `|x' * y'|/`|y'| by apply/(ltr_trans _ lt_axy); rewrite ltr0q.
have lt_0x : 0 < `|x' * y'|.
  by have := lt_0xy; rewrite ltr_pdivl_mulr // mul0r.
have lt_0b : 0 < qb by have := (ltr_trans lt_0xy lt_xyb); rewrite ltr0q.
pose e := Num.min ((`|x' * y'| / `|y'| ) / ratr qa) (ratr qb / (`|x' * y'| / `|y'|)).
have e_gt0 : 0 < e.
  rewrite ltr_minr ltr_pdivl_mulr ?ltr0q // ?mul0r ?mul1r.
  by rewrite lt_0xy /= ltr_pdivl_mulr // mul0r ltr0q lt_0b.
have e_gt1 : Num.sqrt e > 1.
  rewrite -sqrtr1 ltr_sqrt // ltr_minr ltr_pdivl_mulr ?ltr0q // mul1r.
  by rewrite lt_axy /= ltr_pdivl_mulr // mul1r lt_xyb.
have [qe /andP[lt_1qe lte]] := Q_dense_archi e_gt1.
have lt_0qe : 0 < qe by have := (ltr_trans ltr01 lt_1qe); rewrite ltr0q.
have lt_qee : ratr qe * ratr qe < e.
  by rewrite -(sqr_sqrtr (ltrW e_gt0)) expr2 ltr_pmul // ?ler0q ltrW.
have := lt_1qe; rewrite -(ltr_pmulr _ lt_0x).
move/Q_dense_archi => [qx /andP[lt_xqx lt_qxxe]].
have := lt_1qe; rewrite -(ltr_pmulr _ lt_0y).
move/Q_dense_archi => [qy /andP[lt_yqy lt_qyye]].
have Hqinf : ratr qa < ratr (qx / qy / qe) :> fT.
  suff : ratr qa < ratr (qx / qy / qe) :> T by rewrite !ltr_rat.
  apply/(@ltr_trans _ (`|x' * y'|/`|y'|/(ratr qe * ratr qe))).
    rewrite ltr_pdivl_mulr; last by rewrite mulr_gt0 ?ltr0q ?lt_0qe.
    rewrite mulrC -ltr_pdivl_mulr ?ltr0q //; apply/(ltr_le_trans lt_qee).
    by rewrite ler_minl lerr.
  rewrite ltr_pdivr_mulr; last by rewrite mulr_gt0 ?ltr0q.
  rewrite !rmorphM mulrA !fmorphV /= [X in _ < X * _]divfK; last first.
    by rewrite (gtr_eqF) ?ltr0q ?lt_0qe.
  have -> : ratr qx / ratr qy * ratr qe = ratr qx / (ratr qy / ratr qe) :> T.
    by rewrite -mulrA; congr(_ * _); rewrite [RHS]invfM invrK.
  apply/ltr_pmul; rewrite ?invr_ge0 ?normr_ge0 // ltf_pinv //=.
    by rewrite ltr_pdivr_mulr ?ltr0q.
  apply: divr_gt0; first by apply/(ltr_trans lt_0y lt_yqy).
  by rewrite ltr0q lt_0qe.
have Hqsup : ratr (qx * qe / qy) < ratr qb :> fT.
  suff : ratr (qx * qe / qy) < ratr qb :> T. 
    by rewrite ltr_rat [in X in _ -> X]ltr_rat.
  apply/(@ltr_trans _ (`|x' * y'|/`|y'| * (ratr qe * ratr qe))); last first.
    rewrite -ltr_pdivl_mull //; apply/(ltr_le_trans lt_qee); rewrite mulrC.
    by rewrite ler_minl lerr orbT.
  rewrite mulrA -ltr_pdivr_mulr ?ltr0q // [X in _ < X]mulrAC.
  rewrite !rmorphM /= [X in X * _]mulrAC mulfK ?fmorphV /=; last first.
    by rewrite (gtr_eqF) ?ltr0q ?lt_0qe.
  apply/ltr_pmul; rewrite ?invr_ge0 // ?ltf_pinv //=.
  + by apply/ltrW/(ltr_trans lt_0x lt_xqx).
  + by apply/ltrW/(ltr_trans lt_0y lt_yqy).
  by apply/(ltr_trans lt_0y lt_yqy).
have H : 0 < `|yb| by rewrite -(rmorph0 _: ratr 0 = 0 :> fT) -BP_infn ?rmorph0.
rewrite (ltr_trans Hqinf) ?(ltr_trans _ Hqsup) //.
  have -> : qx * qe / qy = qx / (qy / qe) by rewrite invfM invrK mulrAC mulrA.
  rewrite rmorphM fmorphV /=; apply/ltr_pmul; rewrite ?invr_ge0 ?normr_ge0 //.
    by rewrite -BP_supn.
  rewrite ltf_pinv -?BP_infn //; last first.
    rewrite posrE ltr0q divr_gt0 //.
    by have := (ltr_trans lt_0y lt_yqy); rewrite ltr0q.
  by rewrite rmorphM fmorphV /= ltr_pdivr_mulr ?ltr0q.
rewrite mulrAC rmorphM fmorphV /=; apply/ltr_pmul; rewrite ?invr_ge0 //.
+ apply/ltrW; rewrite ltr0q mulr_gt0 ?invr_gt0 //.
  by have := (ltr_trans lt_0x lt_xqx); rewrite ltr0q.
+ by have := ltrW (ltr_trans lt_0y lt_yqy); rewrite !ler0q.
+ by rewrite -BP_infn // rmorphM fmorphV /= ltr_pdivr_mulr ?ltr0q.
rewrite ltf_pinv //= -?BP_supn //.
by have := (ltr_trans lt_0y lt_yqy); rewrite posrE !ltr0q.
Qed.

End BP_morph.

End BetterParams.

Lemma root_annul_realalg_ratr (x : realalg) :
  root (map_poly ratr (annul_realalg x)) x.
Proof.
by have := (root_annul_realalg x); rewrite (eq_map_poly (fmorph_eq_rat _)).
Qed.

Definition from_RA (x : realalg) :=
  BP_val x (annul_realalg x) R.

Lemma minCpoly_neq0_rat (x : {normT algC}) :
  sval (minCpolyP (nval x)) != 0.
Proof. by have [[_ /monic_neq0]] := svalP (minCpolyP (nval x)). Qed.

Lemma root_minCpoly_rat_norm (x : {normT algC}) :
  root (map_poly ratr (sval (minCpolyP (nval x)))) x.
Proof. 
set u := @nval _; have [[H _ _]]:= svalP (minCpolyP (nval x)); move: H.
have /eq_map_poly <- : u \o ratr =1 ratr by apply/fmorph_eq_rat.
move=> H; have := (root_minCpoly (nval x)); rewrite {1}H map_poly_comp.
by rewrite !rootE /= horner_map /=.
Qed.

Definition from_aCR (x : {normT algC}) :=
  BP_val x (sval (minCpolyP (nval x))) R.

Lemma from_RA_is_rmorphism : rmorphism from_RA.
Proof.
split.
  move=> x y; rewrite /from_RA. 
  by apply: BP_valB; rewrite ?root_annul_realalg_ratr ?annul_realalg_neq0.
split; last first.
  by rewrite /from_RA BP_val1 ?root_annul_realalg_ratr ?annul_realalg_neq0.
move=> x y; rewrite /from_RA.
by apply: BP_valM; rewrite ?root_annul_realalg_ratr ?annul_realalg_neq0.
Qed.

Canonical from_RA_rmorphism := RMorphism from_RA_is_rmorphism.

Lemma from_aCR_is_rmorphism : rmorphism from_aCR.
split.
  move=> x y; rewrite /from_aCR. 
  by apply: BP_valB; rewrite ?minCpoly_neq0_rat ?root_minCpoly_rat_norm.
split; last first.
  by rewrite /from_aCR BP_val1 ?minCpoly_neq0_rat ?root_minCpoly_rat_norm.
move=> x y; rewrite /from_aCR.
by apply: BP_valM; rewrite ?minCpoly_neq0_rat ?root_minCpoly_rat_norm.
Qed.

Canonical from_aCR_rmorphism := RMorphism from_aCR_is_rmorphism.


End Algr.

End Archi.

Export Archi.ArchiNumDomain.Exports Archi.ArchiNumField.Exports.
Export Archi.ArchiNumClosedField.Exports Archi.ArchiRealDomain.Exports.
Export Archi.ArchiRealField.Exports Archi.ArchiRealClosedField.Exports.