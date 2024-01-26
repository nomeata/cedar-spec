permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (!({} has "\0\0\0\0\0\0\u{4}&"))
};
