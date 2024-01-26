forbid(
  principal == a::"66666666",
  action in [Action::"action"],
  resource == a::"66666666"
) when {
  ((true && ((a::"66666666"["Bsss"]).containsAll([false, action in principal]))) && (!([false].containsAll([])))) && true
};
