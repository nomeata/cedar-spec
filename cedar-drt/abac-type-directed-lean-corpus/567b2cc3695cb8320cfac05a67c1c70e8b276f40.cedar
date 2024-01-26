permit(
  principal,
  action in [Action::"action"],
  resource == a::"6\u{10}6"
) when {
  false && (a::"6\u{10}6" in resource)
};
