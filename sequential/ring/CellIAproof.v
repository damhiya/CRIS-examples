From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.ring Require Import CellHeader CellI CellA.

(* Simulation Proof *)
Module CellIA. Section CellIA.
  Import CellA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELL: !cellGS}.
  Context (sp_s : specmap) (idx : nat).

  Definition Ist (STATE : stateGS Σ) : iProp Σ :=
    (∃ vany v,
      CellI.v_cv idx ↦tgt vany ∗
      ((cell idx v ∗ auth idx v) ∨
        (⌜vany = v↑⌝ ∗ pending idx ∗ auth idx v)))%I.

  (* Definitions of two Cell modules *)
  Local Definition CellAMod := (CellA.t idx sp_s).
  Local Definition CellIMod := (CellI.t idx).

  Lemma simF_get `{STATE : !stateGS Σ} :
    ⊢ ISim.sim_fun open CellAMod CellIMod Ist (fid (CellHdr.get idx)).
  Proof using.
    cStartFunSim. rewrite /CellI.get.

    (* SRC: precondition *)
    cStepsS. iDestruct "ASM" as "(% & % & C)". subst.
    iDestruct "IST" as (vany v0) "[CV [(C' & A)|(% & P & A)]]".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. cSimpl. rename _q into v.

    iPoseProof (cell_auth_get with "C A") as "%". subst.

    (* TGT: return the value of Cell with [idx] *)
    cStepsT.

    (* SRC: take cSteps *)
    cForcesS. iSplitL "C". { eauto. }

    cStep. iSplit; eauto.
    iExists _, _. iFrame. iRight. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma simF_set `{STATE : !stateGS Σ} :
    ⊢ ISim.sim_fun open CellAMod CellIMod Ist (fid (CellHdr.set idx)).
  Proof using.
    cStartFunSim. rewrite /CellI.set.

    (* SRC: precondition *)
    cStepsS. destruct _q as [v v'].
    iDestruct "ASM" as "(% & % & [P|C])"; subst.
    { (* A case with a resource [P: pending idx] *)
      iDestruct "IST" as (vany v0) "[CV [(C & A)|(% & P' & A)]]"; cycle 1.
      { iExFalso. iApply (pending_unique with "P' P"). }
      des; subst. cSimpl.

      iMod (cell_auth_set with "C A") as "(C & A)".

      (* TGT, SRC: take cSteps *)
      cStepsT.
      cForcesS. iSplitL "C". { eauto. } cStepsS.
      (* Prove the IST *)
      cStep.
      iSplit; eauto.
      iExists _, _. iFrame. iRight. iFrame; eauto.
    }

    (* A case with a resource [C: cell idx v] *)
    iDestruct "IST" as (vany v0) "[CV [(C' & A)|(% & P & A)]]".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. cSimpl.

    iPoseProof (cell_auth_get with "C A") as "%". subst.
    iMod (cell_auth_set with "C A") as "(C & A)".

    (* TGT, SRC: take cSteps *)
    cStepsT.
    cForcesS. iSplitL "C". { eauto. } cStepsS.

    (* Prove the IST *)
    cStep.
    iSplit; eauto.
    iExists _, _. iFrame. iRight. iFrame; eauto.
  (*SLOW*)Qed.

  Theorem sim :
    CellA.init_cond idx ⊢ ISim.t open CellAMod CellIMod Ist.
  Proof.
    cStartModSim.
    - iDestruct "INIT" as (v) "(C & A)".
      iPoseProof (state_init_tgt_acc _ _ (CellI.v_cv idx) with "TGT") as
          (ov) "(%Hcv & CV & _)"; first set_solver.
      unfold CellIMod, CellI.t, SMod.to_mod, CellI.smod in Hcv.
      cbn in Hcv. subst ov.
      iEval (rewrite /CellI.v_cv lookup_insert /=) in "CV".
      iExists (tt↑), v. iFrame.
    - iApply simF_get.
    - iApply simF_set.
  Qed.
End CellIA. End CellIA.
