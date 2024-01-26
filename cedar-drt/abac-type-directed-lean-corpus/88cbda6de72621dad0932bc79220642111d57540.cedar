permit(
  principal in a::"\0pri\0\0\0\0\0\0\u{1}\0\0nci",
  action in [Action::"action"],
  resource == a::"\0pri\0\0\0\0\0\0\u{1}\0\0nci"
) when {
  true
};
