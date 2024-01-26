permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && ((if (a::"" in (-1)) then a::"" else true) == action)) && context
};
