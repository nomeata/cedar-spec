permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (!({} has "\0\0non_head_constraints\0\0"))
};
