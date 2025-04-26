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
    Fork (enqueue "queue" #42) ;;
    dequeue "queue".
End code.

Section inv.
  (* using implicit generalisation for histories, atomics and unique tokens, respectively *)
  Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ}.

  Definition spsc_inv_def (q : loc) (Tok : gname) (γ_tail γ_head : view_inv_pool_name) : vProp Σ := (
    ∃ (V_tail V_head : view) (h_tail h_head : absHist) (t0 t1 : time) (V0 V1 : view),
      @{V_tail} ((q >> tail) sw↦{γ_tail} h_tail) ∗ ((
        ⌜h_tail = {[t0 := (#0, V0)]}⌝
      ) ∨ (
        ∃ (t2 : time) (V2 : view), ⌜
          (t0 < t2)%positive ∧
          h_tail = {[t2 := (#1, V2); t0 := (#0, V0)]}
        ⌝ ∗ (
          UTok Tok ∨
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
  Instance spsc_inv_objective (q : loc) (Tok : gname) (γ_tail γ_head : view_inv_pool_name) :
    Objective (spsc_inv q Tok γ_tail γ_head).
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
    ∀ (q : loc) (Tok : gname) (γ_tail γ_head : view_inv_pool_name) (t0 t1 : time)
      (V0 V1 V_tail V_head : view) (E : coPset),
      @{V_tail} (q >> tail) sw↦{γ_tail} {[t0 := (#0, V0)]} ∗
      @{V_head} (q >> head) sw↦{γ_head} {[t1 := (#0, V1)]} ={E}=∗
        inv (mpN q) (spsc_inv q Tok γ_tail γ_head).
  Proof.
    intros.
    iIntros "(v_tail & v_head)".
    iApply (inv_alloc (mpN q) _ (spsc_inv q Tok γ_tail γ_head)).
    iNext.
    iEval (rewrite spsc_inv_eq).
    iUnfold spsc_inv_def.
    repeat iExists _.
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
    ∀ (tid : thread_id) (q : loc) (Tok : gname) (γ_tail γ_head : view_inv_pool_name)
      (t0 t1 : time) (V0 V1 : view),
    {{{
      inv (mpN q) (spsc_inv q Tok γ_tail γ_head) ∗
      (q >> tail) sw⊒{γ_tail} {[t0 := (#0, V0)]} ∗
      (q >> head) sy⊒{γ_head} {[t1 := (#0, V1)]} ∗
      (q >> buffers) ↦ ?
    }}}
      enqueue #q #42 @ tid; ⊤
    {{{ RET #☠; True }}}.
  Proof.
    intros.
    iIntros "(#invariant & sw_tail & #sy_head & buffers) post".
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
    wp_bind (!ʳˡˣ _)%E.

    iInv "invariant" as "H" "Hclose".
    iEval (rewrite spsc_inv_eq) in "H".
    iUnfold spsc_inv_def in "H".
    iDestruct "H" as (V_tail V_head h_tail h_head t0_H t1_H V0_H V1_H)
      ">(v_tail & v_tail_props & v_head & v_head_props & %constraint)".
    iPoseProof (AtomicPtsTo_AtomicSWriter_agree_1 with "v_tail sw_tail") as "->".

    iApply (AtomicSWriter_read with "[$v_tail $sw_tail $V0]");
      [reflexivity | solve_ndisj | iNext].
    iIntros (t v V V') "((%h & _ & _) & _ & sw_tail & v_tail)".
    apply lookup_singleton_Some in h as [_ [= <- <-]].

    iMod ("Hclose" with "[v_tail v_tail_props v_head v_head_props]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      repeat iExists _.
      iFrame "v_tail v_tail_props v_head v_head_props".
      iPureIntro.
      exact constraint.
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
    iDestruct "v_tail_props" as "[%v_tail_prop1 | v_tail_prop2]"; first last.
    {
      iDestruct "v_tail_prop2" as (t2 V2) "((_ & %impossible) & _)".
      exfalso.
      rewrite map_eq_iff in impossible.
      specialize (impossible t2).
      rewrite lookup_insert in impossible.
      apply lookup_singleton_Some in impossible as [_ [= <- _]].
    }
    apply constraint in v_tail_prop1 as ->.
    apply (lookup_weaken _ _ _ _ h_t) in h_leq_h_head.
    apply lookup_singleton_Some in h_leq_h_head as [-> [= <- <-]].

    iMod ("Hclose" with "[v_tail v_head v_head_props]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      repeat iExists _.
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
      with "[$sw_tail $v_tail $buffers $V0]"
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

    iMod ("Hclose" with "[v_tail v_buffers v_head v_head_props]") as "_";
      [ | iModIntro; iApply "post"; iPureIntro; reflexivity].
    iNext.
    iEval (rewrite spsc_inv_eq).
    iUnfold spsc_inv_def.
    repeat iExists _.
    iFrame "v_tail v_head v_head_props".
    iSplitR "".
    {
      iRight.
      repeat iExists _.
      iSplitR "v_buffers";
        [ | iRight; iExact "v_buffers"].
      iPureIntro.
      split;
        [exact t0_lt_t | reflexivity].
    }
    iPureIntro.
    intro impossible.
    exfalso.
    rewrite map_eq_iff in impossible.
    specialize (impossible t).
    rewrite lookup_insert in impossible.
    symmetry in impossible.
    apply lookup_singleton_Some in impossible as [_ wrong].
    discriminate wrong.
  Qed.

  Lemma spsc_consumer :
    ∀ (tid : thread_id) (q : loc) (Tok : gname) (γ_tail γ_head : view_inv_pool_name)
      (t0 t1 : time) (V0 V1 : view),
    {{{
      inv (mpN q) (spsc_inv q Tok γ_tail γ_head) ∗
      (q >> tail) sy⊒{γ_tail} {[t0 := (#0, V0)]} ∗
      (q >> head) sw⊒{γ_head} {[t1 := (#0, V1)]} ∗
      UTok Tok
    }}}
      dequeue #q @ tid; ⊤
    {{{ v, RET #v; ⌜v = -1 ∨ v = 42⌝ }}}.
  Proof.
    intros.
    iIntros "(#invariant & #sy_tail & sw_head & ⋄) post".
    iPoseProof (AtomicSync_lookup _ _ _ t0 with "sy_tail") as "#V0";
      [rewrite lookup_singleton; reflexivity | ].
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
    apply lookup_singleton_Some in h as [_ [= <- <-]].

    iMod ("Hclose" with "[v_tail v_tail_props v_head v_head_props]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      repeat iExists _.
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
          injection h_leq_h_tail as [= <- _].
          iPureIntro.
          reflexivity.
        }

        iDestruct "v_tail_prop2" as (t2 V2) "((%t0_H_lt_t2 & ->) & _)".
        iPureIntro.
        apply (lookup_weaken _ _ _ _ h_t) in h_leq_h_tail.
        rewrite lookup_insert_ne in h_leq_h_tail;
          [ | lia].
        rewrite lookup_insert in h_leq_h_tail.
        injection h_leq_h_tail as [= <- _].
        reflexivity.
      }

      iMod ("Hclose" with "[v_tail v_tail_props v_head v_head_props]") as "_".
      {
        iNext.
        iEval (rewrite spsc_inv_eq).
        iUnfold spsc_inv_def.
        repeat iExists _.
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
    iDestruct "v_tail_prop2" as (t2 V2) "((%t0_leq_t2 & ->) & resource)".
    apply (lookup_weaken _ _ _ _ h_t) in h_leq_h_tail.
    destruct (decide (t = t2)) as [-> | t_neq_t2]; first last.
    {
      exfalso.
      rewrite lookup_insert_ne in h_leq_h_tail;
        [ | symmetry; exact t_neq_t2].
      rewrite lookup_insert_ne in h_leq_h_tail;
        [ | symmetry; exact t_neq_t0_H].
      rewrite lookup_empty in h_leq_h_tail.
      discriminate h_leq_h_tail.
    }
    rewrite lookup_insert in h_leq_h_tail.
    injection h_leq_h_tail as [= <- <-].
    iDestruct "resource" as "[⋄' | v_buffers]".
    {
      iExFalso.
      iApply (UTok_unique Tok with "⋄ ⋄'").
    }
    iDestruct (view_at_elim V2 with "[V'] v_buffers") as "buffers".
    {
      iApply (monPred_in_mono with "V'").
      simpl.
      transitivity (V0 ⊔ V2);
        [exact (lat_join_sqsubseteq_r V0 V2) | exact V0_and_V_leq_V'].
    }

    iMod ("Hclose" with "[v_tail ⋄ v_head v_head_props]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      repeat iExists _.
      iFrame "v_tail v_head v_head_props".
      iSplitR "";
        [ | iPureIntro; exact constraint].
      iRight.
      repeat iExists _.
      iSplitL "";
        [ | iLeft ; iExact "⋄"].
      iPureIntro.
      split; [exact t0_leq_t2 | reflexivity].
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

    iApply (AtomicSWriter_release_write _ _ _ _ _ _ #1 True with "[$v_head $sw_head $V0]");
      [solve_ndisj | iNext].
    iIntros (t V) "((_ & _ & _) & _ & _ & v_head)".
    iDestruct (AtomicPtsTo_AtomicSeen_latest with "v_tail v_sn_tail") as "%h_leq_h_tail".

    iMod ("Hclose" with "[v_tail v_tail_props v_head]") as "_".
    {
      iNext.
      iEval (rewrite spsc_inv_eq).
      iUnfold spsc_inv_def.
      repeat iExists _.
      iFrame "v_tail v_tail_props v_head".
      iSplitR "".
      {
        iRight.
        repeat iExists _.
        iPureIntro.
        reflexivity.
      }
      iPureIntro.
      intros ->.
      exfalso.
      eapply lookup_weaken in h_t;
        [ | exact h_leq_h_tail].
      apply lookup_singleton_Some in h_t as [_ wrong].
      discriminate wrong.
    }
    clear.
    iModIntro.
    wp_seq.

    (* [6] "buffer" *)
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

    (* [1] let: "queue" := new [ #2 + #capacity ] in *)
    wp_op.
    wp_bind (new _)%E.
    iApply (wp_new);
      [trivial | lia | iPureIntro; reflexivity | iNext].
    iIntros (q) "([_ | %impossible] & nas & _)";
      [ | discriminate impossible].
    repeat iEval (rewrite own_loc_na_vec_cons) in "nas".
    repeat iEval (rewrite shift_lblock_assoc; simpl) in "nas".
    iDestruct "nas" as "(na0 & na1 & na2 & _)".
    iAssert ((q >> 0) ↦ #☠)%I with "[na0]" as "na0";
      [iEval (rewrite shift_lblock_0); iExact "na0" | ].
    wp_let.

    (* [2] "queue" +ₗ #tail <- #0 *)
    wp_op.
    wp_write.

    (* [3] "queue" +ₗ #head <- #0 *)
    wp_op.
    wp_write.
    
    (* [4] "queue" +ₗ #buffers <- #0 *)
    wp_op.
    wp_write.

    (* [5] Fork (enqueue "queue" #42) *)
    wp_bind (Fork _)%E.

    iMod UTok_alloc as (Tok) "⋄".

    iMod (AtomicPtsTo_from_na with "na0") as (γ_tail t0 V0) "(_ & sw_tail & tail)".
    iPoseProof (AtomicSWriter_AtomicSync with "sw_tail") as "#sy_tail".
    iDestruct (view_at_intro with "tail") as (V_tail) "(_ & v_tail)".

    iMod (AtomicPtsTo_from_na with "na1") as (γ_head t1 V1) "(_ & sw_head & head)".
    iDestruct (view_at_intro with "head") as (V_head) "(_ & v_head)".
    iPoseProof (AtomicSWriter_AtomicSync with "sw_head") as "#sy_head".

    iRename "na2" into "buffers".

    iMod (spsc_establish_invariant with "[$v_tail $v_head]") as "#invariant".

    iApply (wp_fork with "[sw_tail buffers]");
      [trivial | | iNext].
    {
      iNext.
      iIntros (thread2).
      iDestruct (own_loc_na_own_loc with "buffers") as "buffers".
      iApply (spsc_producer with "[$invariant $sw_tail $sy_head $buffers]").
      iNext.
      iIntros "_".
      iPureIntro.
      reflexivity.
    }
    iIntros "_".
    wp_seq.

    (* [6] dequeue "queue" *)
    iApply (spsc_consumer with "[$invariant $sy_tail $sw_head $⋄]").
    iNext.
    iExact "post".
  Qed.
End proof.
