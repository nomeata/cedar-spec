permit(
  principal == a::"j",
  action in [Action::"action"],
  resource
) when {
  true && (false has "on_c")
};
