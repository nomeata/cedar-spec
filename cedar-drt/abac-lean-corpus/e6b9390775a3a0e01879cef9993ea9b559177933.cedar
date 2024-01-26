permit(
  principal == a::"\0\0\u{8}",
  action in [Action::"action"],
  resource is a
) when {
  (true && (A::"" < principal)) && principal
};
