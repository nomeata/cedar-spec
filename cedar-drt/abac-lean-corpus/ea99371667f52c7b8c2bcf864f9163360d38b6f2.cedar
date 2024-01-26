permit(
  principal,
  action,
  resource == a::"r"
) when {
  (true && (false == principal)) && (!false)
};
