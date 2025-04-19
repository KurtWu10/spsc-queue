From gpfsl.logic Require Import atomics new_delete proofmode repeat_loop view_invariants.
From gpfsl.examples Require Import uniq_token.

(** Single-producer single-consumer queue, based on gpfsl-examples/mp *)

(* "memory layout" of a queue *)
Local Definition tail := 0%nat.
Local Definition head := 1%nat.
Local Definition buffers := 2%nat.

Section code.
  Definition capacity := 1%nat.

  Definition enqueue (queue buffer : expr) : expr :=
    let: "tail_val" := !ʳˡˣ(queue +ₗ #tail) in
    let: "head_val" := !ᵃᶜ(queue +ₗ #head) in
    if:
      "tail_val" - "head_val" = #capacity
    then
      #-1
    else
      queue +ₗ (#buffers + ("tail_val" `mod` #capacity)) <- buffer ;;
      queue +ₗ #tail <-ʳᵉˡ "tail_val" + #1.

  Definition dequeue (queue : expr) : expr :=
    let: "head_val" := !ʳˡˣ(queue +ₗ #head) in
    let: "tail_val" := !ᵃᶜ(queue +ₗ #tail) in
    if:
      "tail_val" - "head_val" = #0
    then
      #-1
    else
      let: "buffer" := !(queue +ₗ (#buffers + ("head_val" `mod` #capacity))) in
      queue +ₗ #head <-ʳᵉˡ "head_val" + #1 ;;
      "buffer".

  Definition program : expr :=
    let: "queue" := new [ #2 + #capacity ] in
    "queue" +ₗ #tail <- #0 ;;
    "queue" +ₗ #head <- #0 ;;
    "queue" +ₗ #buffers <- #0 ;;
    Fork (
      enqueue "queue" #42
    ) ;;
    dequeue "queue".
End code.

Section inv.
  (* using implicit generalisation for history, atomics and unique token, respectively *)
  Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ}.

  (*
  Reordered from Definition 12.2, invariant for mp

  the two choices of the outer '∨' (with ⌜h = {[t0 := (#0, V0)]}⌝)
  signals that there are two variants inside the invariant

  the invariant represents information related to a single-write atomic with history h under V
  in the first variant, h = {[t0 := (#0, V0)]}, and there is no information on V
  in the second variant, h is extended with a new message,
    and either we have a unique token, or we have the data

  for the producer,
    it only cares about the single-writer ownership (with arbitrary h),
    and can easily establish the invariant after the release write

  for the consumer,
    it requires information of the history h,
    so it exam all possible paths of ∨ and react appropriately

  the complexity of adding read to the producer is that it needs to handle the second branch of ∨,
  i.e. we need a way to prevent the producer from reading the updated value 1
  to do this, we add another unique token to the first branch of ∨ with separation conjunction,
  and also pass the new unique token to the producer
  in this case, the producer is prevented from having the second branch
  *)
  Definition spsc_inv_def (q : loc) (Tok1 Tok2 : gname) (γ_tail γ_head : view_inv_pool_name) : vProp Σ := (
    ∃ (V_tail V_head : view) (h_tail h_head : absHist) (t0 t1 : time) (V0 V1 : view),
      @{V_tail} ((q >> tail) sw↦{γ_tail} h_tail) ∗ ((
        ⌜h_tail = {[t0 := (#0, V0)]}⌝
      ) ∨ (
        UTok Tok2 ∗ ∃ (t2 : time) (V2 : view), ⌜
          (t0 < t2)%positive ∧
          h_tail = {[t2 := (#1, V2); t0 := (#0, V0)]}
        ⌝ ∗ (
          UTok Tok1 ∨
          @{V2} ((q >> buffers) ↦ #42)
        )
      )) ∗
      @{V_head} ((q >> head) sw↦{γ_head} h_head) ∗ ((
        ⌜h_head = {[t1 := (#0, V1)]}⌝
      ) ∨ (
        ∃ (t3 : time) (V3 : view), ⌜
          h_head = {[t3 := (#1, V3); t1 := (#0, V1)]}
        ⌝
      )) ∗ ⌜
        h_tail = {[t0 := (#0, V0)]} → h_head = {[t1 := (#0, V1)]}
      ⌝
  )%I.

  Definition spsc_inv_aux : seal spsc_inv_def.
  Proof. by eexists. Qed.
  Definition spsc_inv := unseal spsc_inv_aux.
  Definition spsc_inv_eq : (spsc_inv = spsc_inv_def) := seal_eq spsc_inv_aux.

  #[global]
  Instance spsc_inv_objective (q : loc) (Tok1 Tok2 : gname) (γ_tail γ_head : view_inv_pool_name) :
    Objective (spsc_inv q Tok1 Tok2 γ_tail γ_head).
  Proof.
    rewrite spsc_inv_eq.
    unfold spsc_inv_def.
    exact _.
  Qed.
End inv.

Section proof.
  Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ}.

  Definition mpN (q : loc) : namespace := nroot .@ "mpN" .@ q.

  Lemma spsc_establish_invariant :
    ∀ (q : loc) (Tok1 Tok2 : gname) (γ_tail γ_head : view_inv_pool_name) (t0 t1 : time)
      (V0 V1 V_tail V_head : view) (E : coPset),
      @{V_tail} (q >> tail) sw↦{γ_tail} {[t0 := (#0, V0)]} ∗
      @{V_head} (q >> head) sw↦{γ_head} {[t1 := (#0, V1)]} ={E}=∗
        inv (mpN q) (spsc_inv q Tok1 Tok2 γ_tail γ_head).
  Proof.
    intros.
    iIntros "(v_tail & v_head)".
    iApply (inv_alloc (mpN q) _ (spsc_inv q Tok1 Tok2 γ_tail γ_head) with "[v_tail v_head]").
    iNext.
    iEval (rewrite spsc_inv_eq).
    iUnfold spsc_inv_def.
    iExists _, _, _, _, _, _, _, _.
    iFrame "v_tail v_head".
    iSplitL "".
    {
      iLeft.
      iPureIntro.
      reflexivity.
    }
    iSplitL "".
    {
      iLeft.
      iPureIntro.
      reflexivity.
    }
    iPureIntro.
    intros _.
    reflexivity.
  Qed.

  Lemma spsc_producer :
    ∀ (tid : thread_id) (q : loc) (Tok1 Tok2 : gname) (γ_tail γ_head : view_inv_pool_name)
      (t0 t1 : time) (V0 V1 : view),
    {{{
      inv (mpN q) (spsc_inv q Tok1 Tok2 γ_tail γ_head) ∗
      (q >> tail) sw⊒{γ_tail} {[t0 := (#0, V0)]} ∗
      (q >> head) sy⊒{γ_head} {[t1 := (#0, V1)]} ∗
      (q >> buffers) ↦ ? ∗
      UTok Tok2
    }}}
      enqueue #q #42 @ tid; ⊤
    {{{ RET #☠; True }}}.
  Proof.
    intros.
    iIntros "(#invariant & sw_tail & sy_head & na1 & ⋄2) post".
    iPoseProof (AtomicSWriter_AtomicSync with "sw_tail") as "#sy_tail".
    iPoseProof (AtomicSync_lookup _ _ _ t0 with "sy_tail") as "#V0".
    {
      rewrite lookup_singleton.
      reflexivity.
    }
    iPoseProof (AtomicSync_AtomicSeen with "sy_head") as "#sn_head".
    iPoseProof (AtomicSync_lookup _ _ _ t1 with "sy_head") as "#V1".
    {
      rewrite lookup_singleton.
      reflexivity.
    }

    unfold enqueue.

    (* [1] let: "tail_val" := !ʳˡˣ(queue +ₗ #tail) in *)
    wp_op.
    wp_bind (!ʳˡˣ_)%E.

    iInv "invariant" as "H" "Hclose".
    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (V_tail V_head h_tail h_head t0_H t1_H V0_H V1_H)
      ">(v_tail & v_tail_props & v_head & v_head_props & %constraint)".
    iPoseProof (AtomicPtsTo_AtomicSWriter_agree_1 with "v_tail sw_tail") as "->".
    iApply (AtomicSWriter_read with "[$v_tail $sw_tail $V0]");
      [trivial | solve_ndisj | iNext].
    iIntros (t v V V') "((%h & _ & _) & _ & sw_tail & v_tail)".
    iDestruct "v_tail_props" as "[%v_tail_prop1 | v_tail_prop2]"; first last.
    {
      iExFalso.
      iDestruct "v_tail_prop2" as "(⋄2' & _)".
      iApply (UTok_unique with "⋄2 ⋄2'").
    }

    destruct (decide (t = t0)) as [-> | t_neq_t0]; first last.
    {
      iExFalso.
      rewrite lookup_insert_ne in h.
      {
        rewrite lookup_empty in h.
        inversion h.
      }
      symmetry.
      apply t_neq_t0.
    }

    rewrite lookup_insert in h.
    symmetry in h.
    inversion h.
    iMod ("Hclose" with "[v_tail v_head v_head_props]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      iExists (V_tail ⊔ V'), _, {[t0 := (#0, V0)]}, _, t0, _, V0, _.
      assert (t0 = t0_H ∧ V0 = V0_H) as [-> ->].
      {
        destruct (decide (t0 = t0_H ∧ V0 = V0_H)) as [[-> ->] | _].
        {
          split; reflexivity.
        }
        rewrite map_eq_iff in v_tail_prop1.
        specialize (v_tail_prop1 t0).
        rewrite lookup_singleton in v_tail_prop1.
        symmetry in v_tail_prop1.
        rewrite lookup_singleton_Some in v_tail_prop1.
        inversion v_tail_prop1 as [-> V0_eq].
        inversion V0_eq.
        split; reflexivity.
      }
      iFrame "v_head v_head_props v_tail".
      iSplitR "";
        [ | iPureIntro; exact constraint].
      iLeft.
      iPureIntro.
      reflexivity.
    }
    clear.
    iModIntro.
    wp_let.

    (* [2] let: "head_val" := !ᵃᶜ(queue +ₗ #head) in *)
    wp_op.
    wp_bind (!ᵃᶜ _)%E.
    iInv "invariant" as "H" "Hclose".

    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (V_tail V_head h_tail h_head t0_H t1_H V0_H V1_H)
      ">(v_tail & v_tail_props & v_head & v_head_props & %constraint)".
    iApply (AtomicSeen_acquire_read with "[$sn_head $v_head $V1]");
      [solve_ndisj | iNext].
    iIntros (t v V V' h) "(
      ((_ & %h_leq_h_head) & %h_t & _ & _) &
      _ & _ & v_head
    )".

    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "v_tail sw_tail") as "->".
    iDestruct "v_tail_props" as "[%v_tail_prop1 | (⋄2' & _)]"; last first.
    {
      iExFalso.
      iApply (UTok_unique with "⋄2 ⋄2'").
    }
    assert (h_head = {[t1_H := (#0, V1_H)]}) as ->.
    {
      apply constraint.
      apply v_tail_prop1.
    }
    apply (lookup_weaken _ _ _ _ h_t) in h_leq_h_head.
    apply lookup_singleton_Some in h_leq_h_head as [-> v_props].
    inversion v_props.
    iMod ("Hclose" with "[v_tail v_head v_head_props]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      iExists _, _, _, _, _, _, _, _.
      iFrame "v_tail v_head v_head_props".
      iSplitR "".
      {
        iLeft.
        iPureIntro.
        reflexivity.
      }
      iPureIntro.
      intros _.
      reflexivity.
    }
    clear.
    iModIntro.
    wp_let.

    (* [3] if: "tail_val" - "head_val" = #capacity *)
    wp_op.
    wp_op.
    wp_if.

    (* [4] queue +ₗ (#buffers + ("tail_val" `mod` #capacity)) <- #42 *)
    wp_op.
    wp_op.
    wp_op.
    wp_write.

    (* [5] queue +ₗ #tail <-ʳᵉˡ "tail_val" + #1 *)
    wp_op.
    wp_op.
    iInv "invariant" as "H" "Hclose".
    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (V_tail V_head h_tail h_head t0_H t1_H V0_H V1_H)
      ">(v_tail & v_tail_props & v_head & v_head_props & %constraint)".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "v_tail sw_tail") as "->".
    iApply (
      AtomicSWriter_release_write _ _ _ _ _ _ #1 ((q >> buffers) ↦ #42)
      with "[$sw_tail $v_tail $na1 $V0]"
    );
      [solve_ndisj | iNext].
    iIntros (t V) "((%t_prop & _) & _ & (v_buffers & _) & v_tail)".
    assert (t0 < t)%positive as t0_lt_t.
    {
      unfold fresh_max_time in t_prop.
      apply t_prop.
      rewrite lookup_insert.
      eexists.
      reflexivity.
    }

    iMod ("Hclose" with "[v_tail v_buffers ⋄2 v_tail_props v_head v_head_props]") as "_";
      [| iModIntro; iApply "post"; iPureIntro; reflexivity].
    iNext.
    iEval (rewrite spsc_inv_eq).
    iUnfold spsc_inv_def.
    iExists (V_tail ⊔ V), _, {[t := (#1, V); t0 := (#0, V0)]}, _, t0, _, V0, _.
    iFrame "v_tail v_head v_head_props".
    iSplitR "".
    {
      iRight.
      iFrame "⋄2".
      iExists t, V.
      iSplitR "v_buffers";
        [| iRight; iExact "v_buffers"].
      iPureIntro.
      split;
        [exact t0_lt_t | reflexivity].
    }
    iPureIntro.
    clear -t0_lt_t.
    intro impossible.
    exfalso.
    rewrite map_eq_iff in impossible.
    specialize (impossible t).
    rewrite lookup_insert in impossible.
    symmetry in impossible.
    rewrite lookup_singleton_Some in impossible.
    destruct impossible as [-> _].
    lia.
  Qed.

  Lemma spsc_consumer :
    ∀ (tid : thread_id) (q : loc) (Tok1 Tok2 : gname) (γ_tail γ_head : view_inv_pool_name)
      (t0 t1 : time) (V0 V1 : view),
    {{{
      inv (mpN q) (spsc_inv q Tok1 Tok2 γ_tail γ_head) ∗
      (q >> tail) sy⊒{γ_tail} {[t0 := (#0, V0)]} ∗
      (q >> head) sw⊒{γ_head} {[t1 := (#0, V1)]} ∗
      UTok Tok1
    }}}
      dequeue #q @ tid; ⊤
    {{{ v, RET #v; ⌜v = -1 ∨ v = 42⌝ }}}.
  Proof.
    intros.
    iIntros "(#invariant & #sy_tail & sw_head & ⋄1) post".
    iPoseProof (AtomicSync_lookup _ _ _ t0 with "sy_tail") as "#V0".
    {
      rewrite lookup_singleton.
      reflexivity.
    }
    iPoseProof (AtomicSync_AtomicSeen with "sy_tail") as "#sn_tail".

    unfold dequeue.

    (* [1] let: "head_val" := !ʳˡˣ(queue +ₗ #head) in *)
    wp_op.
    wp_bind (!ʳˡˣ _)%E.
    iInv "invariant" as "H" "Hclose".
    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (V_tail V_head h_tail h_head t0_H t1_H V0_H V1_H)
      ">(v_tail & v_tail_props & v_head & v_head_props & %constraint)".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "v_head sw_head") as "->".
    iApply (AtomicSWriter_read with "[$v_head $sw_head $V0]");
      [reflexivity | solve_ndisj | iNext].
    iIntros (t v V V') "((%h & _ & _) & _ & sw_head & v_head)".
    destruct (decide (t = t1)) as [-> | t_neq_t1]; last first.
    {
      exfalso.
      rewrite lookup_insert_ne in h;
        [rewrite lookup_empty in h; inversion h | symmetry; exact t_neq_t1].
    }
    rewrite lookup_insert in h.
    symmetry in h.
    inversion h.
    iMod ("Hclose" with "[v_tail v_tail_props v_head v_head_props]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      iExists _, _, _, _, _, _, _, _.
      iFrame "v_tail v_tail_props v_head v_head_props".
      iPureIntro.
      exact constraint.
    }
    clear.
    iModIntro.
    wp_let.

    (* [2] let: "tail_val" := !ᵃᶜ(queue +ₗ #tail) in *)
    wp_op.
    wp_bind (!ᵃᶜ _)%E.
    iInv "invariant" as "H" "Hclose".

    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (V_tail V_head h_tail h_head t0_H t1_H V0_H V1_H)
      ">(v_tail & v_tail_props & v_head & v_head_props & %constraint)".

    iApply (AtomicSeen_acquire_read with "[$sn_tail $v_tail $V0]");
      [solve_ndisj | iNext].
    iIntros (t v V V' h) "(
      ((_ & %h_leq_h_tail) & %h_t & _ & %V0_and_V_leq_V') &
      #V' & #v_sn_tail & v_tail
    )".

    destruct (decide (t = t0_H)) as [-> | t_neq_t0_H].
    {
      iAssert (⌜v = #0⌝)%I as "->".
      {
        iDestruct "v_tail_props" as "[v_tail_prop1 | v_tail_prop2]".
        {
          iDestruct "v_tail_prop1" as "->".
          apply (lookup_weaken _ _ _ _ h_t) in h_leq_h_tail.
          rewrite lookup_insert in h_leq_h_tail.
          inversion h_leq_h_tail.
          iPureIntro.
          reflexivity.
        }

        iDestruct "v_tail_prop2" as "(_ & v_tail_prop2)".
        iDestruct "v_tail_prop2" as (t2 V2) "((%t0_H_lt_t2 & ->) & _)".
        iPureIntro.
        apply (lookup_weaken _ _ _ _ h_t) in h_leq_h_tail.
        rewrite lookup_insert_ne in h_leq_h_tail.
        {
          rewrite lookup_insert in h_leq_h_tail.
          inversion h_leq_h_tail.
          reflexivity.
        }
        lia.
      }

      iMod ("Hclose" with "[v_tail v_tail_props v_head v_head_props]") as "_".
      {
        iNext.
        iEval (rewrite spsc_inv_eq).
        iUnfold spsc_inv_def.
        iExists (V_tail ⊔ V'), _, h_tail, _, t0_H, _, V0_H, _.
        iFrame "v_tail v_tail_props v_head v_head_props".
        iPureIntro.
        exact constraint.
      }
      clear.
      iModIntro.
      wp_let.

      (* [3] if: "tail_val" - "head_val" = #0 *)
      wp_op.
      wp_op.
      wp_if.

      iApply "post".
      iPureIntro.
      left.
      reflexivity.
    }

    iDestruct "v_tail_props" as "[v_tail_prop1 | v_tail_prop2]".
    {
      iDestruct "v_tail_prop1" as "->".
      exfalso.
      apply (lookup_weaken _ _ _ _ h_t) in h_leq_h_tail.
      apply lookup_singleton_Some in h_leq_h_tail as [-> _].
      apply t_neq_t0_H.
      reflexivity.
    }

    iDestruct "v_tail_prop2" as "(⋄2 & v_tail_prop2)".
    iDestruct "v_tail_prop2" as (t2 V2) "((%t0_leq_t2 & ->) & resource)".

    apply (lookup_weaken _ _ _ _ h_t) in h_leq_h_tail.
    assert (t = t2) as ->.
    {
      destruct (decide (t = t2)) as [-> | t_neq_t2];
        [reflexivity | ].

      exfalso.

      rewrite lookup_insert_ne in h_leq_h_tail;
        [| symmetry; exact t_neq_t2].
      rewrite lookup_insert_ne in h_leq_h_tail;
        [rewrite lookup_empty in h_leq_h_tail; inversion h_leq_h_tail | symmetry; exact t_neq_t0_H].
    }
    rewrite lookup_insert in h_leq_h_tail.
    inversion h_leq_h_tail as ([H1 H2]).
    destruct H1.
    destruct H2.

    iDestruct "resource" as "[⋄1' | v_buffers]".
    {
      iExFalso.
      iApply (UTok_unique Tok1 with "⋄1 ⋄1'").
    }

    iDestruct (view_at_elim V2 _ with "[V'] v_buffers") as "buffers".
    {
      iApply (monPred_in_mono _ _ with "V'").
      simpl.
      transitivity (V0 ⊔ V2);
        [exact (lat_join_sqsubseteq_r V0 V2) | exact V0_and_V_leq_V'].
    }

    iMod ("Hclose" with "[v_tail ⋄1 ⋄2 v_head v_head_props]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      iExists (V_tail ⊔ V'), _, {[t2 := (#1, V2); t0_H := (#0, V0_H)]}, _, t0_H, _, V0_H, _.
      iFrame "v_tail v_head v_head_props".
      iSplitR "";
        [ |iPureIntro; exact constraint].
      iRight.
      iFrame "⋄2".
      iExists t2, V2.
      iSplitL "";
        [iPureIntro; split; [exact t0_leq_t2 | reflexivity] | ].
      iLeft.
      iExact "⋄1".
    }
    clear - h_t.
    iModIntro.
    wp_let.

    (* [3] if: "tail_val" - "head_val" = #0 *)
    wp_op.
    wp_op.
    wp_if.

    (* [4] let: "ret" := !(queue +ₗ (#buffers + ("head_val" `mod` #capacity))) in in *)
    wp_op.
    wp_op.
    wp_op.
    wp_read.
    wp_let.

    (* [5] queue +ₗ #head <-ʳᵉˡ "head_val" + #1 *)
    wp_op.
    wp_op.
    wp_bind (_ <-ʳᵉˡ _)%E.
    iInv "invariant" as "H" "Hclose".
    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (V_tail V_head h_tail h_head t0_H t1_H V0_H V1_H)
      ">(v_tail & v_tail_props & v_head & v_head_props & %constraint)".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "v_head sw_head") as "->".
    (* ⊒V0 here is release arbitrarily, otherwise there is an unknown shelved goal *)
    iApply (AtomicSWriter_release_write _ _ _ _ _ _ #1 (⊒V0) with "[$v_head $sw_head $V0]");
      [solve_ndisj | iNext].
    iIntros (t V) "((_ & _ & _) & #V & _ & v_head)".
    iDestruct (AtomicPtsTo_AtomicSeen_latest with "v_tail v_sn_tail") as "%h_leq_h_tail".
    iMod ("Hclose" with "[v_tail v_tail_props v_head v_head_props]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      iExists _, _, _, _, _, _, _, _.
      iFrame "v_tail v_tail_props v_head".
      iSplitR "".
      {
        iRight.
        iExists t, V.
        iPureIntro.
        reflexivity.
      }
      iPureIntro.
      intro impossible.
      exfalso.
      assert (h_tail !! t2 = Some (#1, V2)) as h_tail_t2.
      {
        apply (lookup_weaken h h_tail t2 (#1, V2) h_t h_leq_h_tail).
      }
      assert (t0_H = t2 ∧ (#0, V0_H) = (#1, V2)) as wrong.
      {
        rewrite <- (lookup_singleton_Some t0_H t2 (#0, V0_H) (#1, V2)).
        rewrite impossible in h_tail_t2.
        apply h_tail_t2.
      }
      destruct wrong as [_ wrong].
      inversion wrong.
    }
    clear.
    iModIntro.
    wp_seq.

    iApply "post".

    iPureIntro.
    right.
    reflexivity.
  Qed.

  Lemma spsc_instance_gen_inv :
    ∀ (tid : thread_id),
    {{{ True }}}
      program @ tid; ⊤
    {{{ v, RET #v; ⌜v = -1 ∨ v = 42⌝ }}}.
  Proof.
    iIntros (thread1 Φ) "_ post".

    unfold program.
    unfold enqueue.
    unfold dequeue.

    wp_op.
    wp_apply wp_new;
      [done.. | ].
    iIntros (q) "([_ | %impossible] & nas & _)";
      [| discriminate impossible].
    repeat iEval (rewrite own_loc_na_vec_cons) in "nas".
    repeat iEval (rewrite shift_lblock_assoc; simpl) in "nas".
    iDestruct "nas" as "(na0 & na1 & na2 & _)".
    iAssert ((q >> 0) ↦ #☠)%I with "[na0]" as "na0";
      [iEval (rewrite shift_lblock_0); iExact "na0" | ].

    wp_let.
    wp_op.
    wp_write.
    repeat (wp_op; wp_write).

    iMod UTok_alloc as (Tok1) "⋄1".
    iMod UTok_alloc as (Tok2) "⋄2".

    iMod (AtomicPtsTo_from_na with "na0") as (γ_tail t0 V0) "(_ & sw_tail & tail)".
    iPoseProof (AtomicSWriter_AtomicSync with "sw_tail") as "#sy_tail".
    iDestruct (view_at_intro with "tail") as (V_tail) "(_ & v_tail)".

    iMod (AtomicPtsTo_from_na with "na1") as (γ_head t1 V1) "(_ & sw_head & head)".
    iDestruct (view_at_intro with "head") as (V_head) "(_ & v_head)".
    iPoseProof (AtomicSWriter_AtomicSync with "sw_head") as "#sy_head".

    iRename "na2" into "buffers".

    iMod (spsc_establish_invariant with "[$v_tail $v_head]") as "#invariant".

    wp_apply (wp_fork with "[sw_tail buffers ⋄2]");
      [trivial | ..].
    {
      iNext.
      iIntros (thread2).
      iDestruct (own_loc_na_own_loc with "buffers") as "buffers".
      wp_apply (spsc_producer with "[$invariant $sw_tail $sy_head $buffers $⋄2]").
      iIntros "_".
      iPureIntro.
      reflexivity.
    }

    iIntros "_".
    wp_seq.
    wp_apply (spsc_consumer with "[$invariant $sy_tail $sw_head $⋄1]").
    iApply "post".
  Qed.
End proof.
