
From MatchingLogic Require Import Signature locally_nameless DefaultVariables Theories.Definedness Theories.Sorts.

Module LTL.
  Import MLNotations.

  Record LTLSignature :=
    { AP : Set;
      AP_dec : forall (a1 a2 : AP), {a1 = a2} + {a1 <> a2};
    }.
  
  
  Section LTL.
    (* We are parametrized with a set of atomic proposition. *)
    Context {ltlsig : LTLSignature}.

    Inductive Symbols :=
    | sym_import_definedness (d : Definedness.Symbols)
    | sym_import_sorts (s : Sorts.Symbols)
    | sym_SortInitialState
    | sym_SortState
    | sym_next
    | sym_prev
    | sym_a (ap : AP ltlsig)
    .

    Lemma Symbols_dec : forall (s1 s2 : Symbols), {s1 = s2} + {s1 <> s2}.
    Proof.
      decide equality.
      * decide equality.
      * decide equality.
      * apply (AP_dec ltlsig).
    Qed.

    
    Let signature : Signature :=
      {| symbols := Symbols;
         sym_eq := Symbols_dec;
         variables := DefaultMLVariables;
      |}.
    #[local]
     Canonical Structure signature.

    Instance definedness_syntax : Definedness.Syntax :=
      {|
         Definedness.inj := sym_import_definedness;
      |}.

    Instance sorts_syntax : Sorts.Syntax :=
      {|
      Sorts.inj := sym_import_sorts;
      Sorts.imported_definedness := definedness_syntax;
      |}.


    Let sym (s : Symbols) : @Pattern signature :=
      @patt_sym signature s.
    Let evar (sname : string) : @Pattern signature :=
      @patt_free_evar signature (find_fresh_evar_name (@evar_c sname) nil).
    Let svar (sname : string) : @Pattern signature :=
      @patt_free_svar signature (find_fresh_svar_name (@svar_c sname) nil)
    .

    Notation "A → B" := (patt_imp A B) (at level 90, right associativity, B at level 200) : ml_scope.
    Notation "A /\ B" := (patt_and A B) (at level 80, right associativity) : ml_scope.
    Notation "A ‌\/ B" := (patt_or A B) (at level 85, right associativity) : ml_scope.
    Notation "∃, A" := (ex, A) (at level 55) : ml_scope.
    Notation "μ, A" := (mu, A) (at level 55) : ml_scope.
    Notation "A == B" := (patt_equal A B) (at level 100) : ml_scope.
    Notation "A ∈ B" := (patt_in A B) (at level 70) : ml_scope.
    Notation "A ⊆ B" := (patt_subseteq A B) (at level 70) : ml_scope.
    Notation "⊥" := (patt_bott) : ml_scope.

    Notation "[[ A ]]" := (inhabitant_set A) : ml_scope.

    (* Element variables - free *)
    Notation x := (evar "x").
    Notation y := (evar "y").
    Notation z := (evar "z").

    (* Element variables - bound *)
    Notation b0 := (patt_bound_evar 0).
    Notation b1 := (patt_bound_evar 1).

    (* Set variables - bound *)
    Notation B0 := (patt_bound_svar 0).


    Definition patt_partial_function(phi from to : Pattern) : Pattern :=
      patt_forall_of_sort from (patt_exists_of_sort to ((phi $ b1) ⊆ b0)).

    Notation "A : B ⇀ C" := (patt_partial_function A B C) (at level 80) : ml_scope.
    
    Notation InitialState := (sym sym_SortInitialState).
    Notation State := (sym sym_SortState).

    Definition next (phi : Pattern) : Pattern :=
      patt_app (sym sym_next) phi.
    
    Definition prev (phi : Pattern) : Pattern :=
      patt_app (sym sym_prev) phi.
    
    Notation "∘ X" := (next X) (at level 50) : ml_scope.

    Inductive AxiomName :=
    | AxImportedDefinedness (name : Definedness.AxiomName) (* imports axioms from the Definedness module *)
    | AxPrev
    | AxInitialState (* Trace *)
    | AxState (* TraceSuffix *)
    | AxInf
    | AxNextOut
    | AxNextPFun
    | AxNextInj
    | AxAtomicProp (ap : AP ltlsig) (* defines a potentially infinite class of axioms *)
    .

    Definition axiom(name : AxiomName) : @Pattern signature :=
      match name with
      | AxImportedDefinedness name' => Definedness.axiom name'
                                                         
      | AxPrev
        => (prev x == (∃, b0 /\ (x ∈ ∘b0 )))%ml
                                            
      | AxInitialState
        => (∃,([[ InitialState ]] == b0))%ml
                                         
      | AxState
        => ([[ State ]] == (μ, ([[ InitialState ]] or (prev B0))))%ml

      | AxInf
        => ([[ State ]] ⊆ ∘ ([[ State ]]))%ml

      | AxNextOut
        => ((∘(¬([[ State ]]))) ⊆ (¬ [[ State ]]))%ml

      | AxNextPFun
        => (sym sym_next) : State ⇀ State

      | AxNextInj
        => patt_forall_of_sort State (patt_forall_of_sort State ( ( (∘b0 == ∘b1) and (¬ (∘b1 == ⊥))  ) --> (b0 == b1)  ))

      | AxAtomicProp a
        => (sym (sym_a a)) ⊆ [[ State ]]
      end.


    Definition satisfies_axioms (M : Model) := forall (ax_name : AxiomName),    
        satisfies_model M (axiom ax_name).
    
    
  End LTL.

End LTL.
