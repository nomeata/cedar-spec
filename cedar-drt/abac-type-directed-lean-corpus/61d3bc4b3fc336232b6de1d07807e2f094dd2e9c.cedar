permit(
  principal == a::"\0pri\0\0\0\0\0\0\0\0\0ons",
  action in [Action::"action"],
  resource == a::"\0pri\0\0\0\0\0\0\0\0\0ons"
) when {
  true && (!false)
};
