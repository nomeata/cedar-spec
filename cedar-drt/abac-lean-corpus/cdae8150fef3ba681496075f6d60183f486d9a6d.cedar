permit(
  principal == a::"\0",
  action == Action::"action",
  resource == a::"\0"
) when {
  (true && "\u{1a}\u{1a}") && (principal has "\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}A\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}\u{1a}")
};
