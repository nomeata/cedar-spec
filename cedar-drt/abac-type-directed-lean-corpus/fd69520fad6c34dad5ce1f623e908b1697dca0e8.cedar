permit(
  principal == a::"\0\0\0\06666",
  action in [Action::"action"],
  resource is a in a::"\0\0\0\06666"
) when {
  false
};
