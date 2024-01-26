permit(
  principal is a,
  action in [Action::"action"],
  resource == a::"\n\nijc\u{2}jjj"
) when {
  true && action
};
