permit(
  principal == a::"\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}66",
  action in [Action::"action"],
  resource is a in a::"\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}66"
) when {
  false
};
