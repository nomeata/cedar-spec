@M("")
permit(
  principal in a::"\0",
  action in [Action::"action"],
  resource == a::"\0"
) when {
  true && ((ip("******************context*******************\u{1e}\u{1e}\u{1e}\0\0")) == (!(principal <= principal)))
};
