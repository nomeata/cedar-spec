forbid(
  principal == a::"jj\\ccccc",
  action in [Action::"action"],
  resource
) when {
  (false && (a::"jj\\ccccc" in a::"jj\\ccccc")) && a::"jj\\ccccc"
};
