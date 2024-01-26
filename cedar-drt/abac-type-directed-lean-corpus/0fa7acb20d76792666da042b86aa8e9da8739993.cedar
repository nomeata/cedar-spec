permit(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  true && (if (!(principal in resource)) then true else true)
};
