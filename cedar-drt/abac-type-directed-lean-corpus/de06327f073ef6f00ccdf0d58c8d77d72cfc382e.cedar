permit(
  principal,
  action in [A::Action::"action"],
  resource
) when {
  (true && (principal in principal)) && (action has "")
};
