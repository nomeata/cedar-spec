permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && [i::"j\u{13}", a::"", !principal]) && principal
};
