permit(
  principal,
  action,
  resource == a::"j"
) when {
  (true && (((action in principal) || principal) || principal)) && resource
};
