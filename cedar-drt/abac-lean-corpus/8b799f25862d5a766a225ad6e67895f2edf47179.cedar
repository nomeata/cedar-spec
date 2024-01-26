permit(
  principal == a::"\0\0pl",
  action in [Action::"action"],
  resource == a::"\0\0pl"
) when {
  true && (Action::"action".greaterThanOrEqual("" < a::"\0\0pl"))
};
