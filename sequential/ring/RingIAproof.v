From CRIS.common Require Import CRIS.
From CRIS.lib Require Import BiEnrichedProset.

From CRIS.ring Require Import RingHeader CellHeader RingA CtrlI CellA CellI
  CtrlIAproof CellIAproof.

(* Contextual Refinement Proof *)
Module RingIA. Section RingIA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELL: !cellGS}.

  Definition CellIG start len :=
    Mod.addL (List.map CellI.t (seq start len)).

  Lemma ctxr max_size (sps spt : specmap) :
    RingA.init_cond max_size ∗
      ([∗ list] i↦x ∈ seq 0 max_size, CellA.init_cond i) ⊢
    ctx_refines
      (CtrlI.t max_size ★ CellIG 0 max_size)
      (RingA.t max_size sps ★ CtrlIA.CellG spt 0 max_size).
  Proof using.
    assert (Hcells : ∀ n,
      ([∗ list] i↦x ∈ seq 0 n, CellA.init_cond i) ⊢
        ctx_refines (CellIG 0 n) (CtrlIA.CellG spt 0 n)).
    { intros n. induction n as [|n IH].
      + iIntros "_". rewrite /CellIG /CtrlIA.CellG /CtrlIA.CellGS /=.
        iApply ctxr_refl.
      + rewrite /CellIG /CtrlIA.CellG /CtrlIA.CellGS.
        rewrite !seq_S !map_app !mod_addL_app big_sepL_app.
        iIntros "[HCs HC]".
        rewrite /= !right_id length_seq.
        jIntros (ctx_refines_BiProset) "(CELLS & CELL)".
        jPoseProof IH with "HCs" "CELLS" as "CELLS".
        jPoseProof main_adequacy with "HC" "CELL" as "CELL".
        { eapply (CellIA.sim spt). }
        jFrame.
    }
    iIntros "[HR HC]".
    jIntros (ctx_refines_BiProset) "(CTRL & CELLS)".
    jPoseProof (Hcells max_size) with "HC" "CELLS" as "CELLS".
    jPoseProof main_adequacy with "HR" "[CTRL CELLS]" as "M".
    { eapply (CtrlIA.sim max_size spt sps). }
    { jFrame. }
    jFrame.
  Qed.

End RingIA. End RingIA.
