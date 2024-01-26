permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a
) when {
  (true && (((context has "B") in (action is a)) in A0::"")) && principal
};
