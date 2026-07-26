From CRIS.common Require Import CRIS.
From CRIS.lib Require Import BiEnrichedProset.
From CRIS.imp_system.mem Require Import MemA.
From CRIS.map Require Export MapHeader MapA MapM MapI MapIMproof MapMAproof.

Module MapIA. Section MapIA.
  Context `{!crisG Γ Σ α β τ _S _I, _MAPM: !mapMGS, _MAP: !mapGS, _MEM: !memGS}.

  Lemma ctxr (sp_s sp_mem : specmap)
      (MapInSpMap : MapA.sp ⊆ sp_s) :
    MapA.init_cond ⊢
      ctx_refines
        (MapI.t ★ MemA.t sp_mem)
        (MapA.t sp_s ★ MemA.t sp_mem).
  Proof.
    assert (MapMInSpMap : MapM.sp ⊆ MapM.sp) by reflexivity.
    iIntros "H".
    iPoseProof
      (MapIM.ctxr MapM.sp sp_mem MapMInSpMap) as "REF".
    iPoseProof
      (MapMA.ctxr sp_s MapM.sp MapInSpMap MapMInSpMap with "H")
      as "MAP_REF".
    jIntros (ctx_refines_BiProset) "SRC".
    jPoseProof "REF" with "SRC" as "(MAP & MEM)".
    jPoseProof "MAP_REF" with "MAP" as "MAP".
    jSplitL "MAP"; [jApply "MAP"|jApply "MEM"].
  Qed.
End MapIA. End MapIA.
