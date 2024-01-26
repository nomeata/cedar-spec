permit(
  principal,
  action,
  resource
) when {
  (true && (principal has "")) && (action has "")
};
