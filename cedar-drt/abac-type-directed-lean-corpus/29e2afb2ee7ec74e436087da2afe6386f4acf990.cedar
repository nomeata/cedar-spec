permit(
  principal is a in a::"6\06",
  action in [Action::"action"],
  resource == a::"6\06"
) when {
  true && (action in action)
};
