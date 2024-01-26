permit(
  principal == a::"\0\0\0\06",
  action in [Action::"action"],
  resource is a in a::"\0\0\0\06"
) when {
  true && (!(resource in action))
};
