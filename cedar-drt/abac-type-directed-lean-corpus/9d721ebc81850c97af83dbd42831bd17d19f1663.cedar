@B("6666")
permit(
  principal in EmrYrgmlq::Bm0s::"3",
  action == EmrYrgmlq::Action::"action",
  resource == EmrYrgmlq::Bm0s::"3"
) when {
  (true && ((if ((decimal("0.1")).lessThan(decimal("0.1"))) then [] else []).containsAll([]))) && true
};
