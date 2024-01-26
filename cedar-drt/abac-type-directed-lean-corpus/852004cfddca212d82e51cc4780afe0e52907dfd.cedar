@A("\0\0A")
permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (!({"": false} has "\0"))
};
