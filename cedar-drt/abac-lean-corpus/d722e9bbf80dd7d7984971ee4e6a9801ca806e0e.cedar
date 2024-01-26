permit(
  principal == a::"jj",
  action in [Action::"action"],
  resource == a::"jj"
) when {
  (true && (([true, Action::"action", false].containsAll(a::"" in a::"jj")) == context)) && a::""
};
