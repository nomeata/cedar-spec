permit(
  principal,
  action in [Action::"action"],
  resource is a in a::"6"
) when {
  (true && (action has "\t\u{6}id")) && true
};
