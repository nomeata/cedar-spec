permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (!({"\n\0\0\0\u{19}\0\0\0\0\0\0\0\0\0\0\0\0\0strai\0\0": false} has "\0"))
};
