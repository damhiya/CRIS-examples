From CRIS.common Require Import CRIS.
From CRIS.filter Require Import CallFilter.
From CRIS.single_coin Require Export SingleCoinHeader SingleCoinI SingleCoinP.
From CRIS.prophecy Require Export ProphecyHeader ProphecyI.

Module SingleCoinIP. Section SingleCoinIP.
  Import SingleCoinP SingleCoinI.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context (mn : string).

  Local Notation MA := (SingleCoinP.t mn ★ ProphecyI.t mn).
  Local Notation MI := (CFilter.filter (Prophecy.exports mn) SingleCoinI.t ★ ProphecyI.t mn).

  Local Definition Ist (STATE : stateGS Σ) : iProp Σ :=
    (∃ (l : list (option bool)),
      SingleCoinP.v_coins ↦src l↑ ∗ SingleCoinI.v_coins ↦tgt l↑)%I.

  Local Definition IstFull :=
    (λ STATE, (Ist STATE ∗ IstEq (ProphecyI.t mn) STATE)%I).

  Lemma simF_new :
    ⊢ ISim.sim_fun open MA MI IstFull (fid SingleCoinHdr.new).
  Proof.
    cStartFunSim. rewrite /SingleCoinI.new /SingleCoinP.new.
    iDestruct "IST" as "[IST EQ]".
    iDestruct "IST" as (l) "[COINSS COINST]".
    cStepsS. cStepsT. destruct Any.downcast; cStepsS; last case_match; cStepsS; ss.
    cStepsS. cStepsT.
    cInlineS. rewrite /ProphecyI.new. cStepsS. cStep.
    iSplit; eauto. iSplitR "EQ".
    - iExists (l ++ [None]). iFrame.
    - iFrame.
  Qed.

  Lemma simF_read :
    ⊢ ISim.sim_fun open MA MI IstFull (fid SingleCoinHdr.read).
  Proof.
    cStartFunSim. rewrite /SingleCoinI.read /SingleCoinP.read.
    iDestruct "IST" as "[IST EQ]".
    iDestruct "IST" as (l) "[COINSS COINST]".
    cStepsS. cStepsT. destruct (Any.downcast arg); cStepsS; last case_match; cStepsS; ss.
    cStepsS. cStepsT. des_ifs.
    { cStep; eauto. iSplit; eauto.
      iSplitR "EQ"; last iFrame. iExists l. iFrame.
    }
    { cStepsT. cForceS _q. cStepsS. rewrite /v_coins /SingleCoinP.v_coins.
      cStepsS. cStepsT.
      cInlineS. rewrite /ProphecyI.new. cStepsS. cStep. iSplit; eauto.
      iSplitR "EQ"; last iFrame. iExists _. iFrame.
    }
    { rewrite /triggerUB. cStepsS. des_ifs; cStepsS; ss. }
  Qed.

  Lemma sim : ⊢ ISim.t open MA MI IstFull.
  Proof.
    iApply (ISim_reflR open (SingleCoinP.t mn)
      (CFilter.filter (Prophecy.exports mn) SingleCoinI.t)
      (ProphecyI.t mn) Ist).
    - rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro. mod_tac. }
      iIntros (STATE) "SRC TGT".
      iPoseProof (state_init_src_acc _ _ v_coins with "SRC") as
          (ovs) "(%Hsrc & COINSS & _)"; first set_solver.
      iPoseProof (state_init_tgt_acc _ _ v_coins with "TGT") as
          (ovt) "(%Htgt & COINST & _)"; first set_solver.
      simpl_map. subst ovs ovt. iExists []. iFrame.
    - rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split.
        - mod_tac.
        - mod_tac.
      }
      iIntros (fn) "%Hfn".
      repeat rewrite Mod.dom_fnsems_add in Hfn.
      set_unfold in Hfn; des; subst.
      + iApply simF_new.
      + iApply simF_read.
  Qed.
End SingleCoinIP. End SingleCoinIP.
