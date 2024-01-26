permit(
  principal,
  action in [Action::"action"],
  resource in a::"b"
) when {
  (true && (a::"b" == action)) && (!Action::"action")
};
