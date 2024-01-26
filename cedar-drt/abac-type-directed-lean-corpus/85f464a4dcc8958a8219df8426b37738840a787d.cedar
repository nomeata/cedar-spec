permit(
  principal is a,
  action in [Action::"action"],
  resource is a in a::"\0\0"
) when {
  (true && (principal has "\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0")) && true
};
