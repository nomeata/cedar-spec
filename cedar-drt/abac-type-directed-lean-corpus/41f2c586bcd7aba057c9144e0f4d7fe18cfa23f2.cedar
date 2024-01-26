permit(
  principal,
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::"\0\06"
) when {
  (true && (a::"\0\06" in principal)) && false
};
