forbid(
  principal,
  action,
  resource == a::"2"
) when {
  true && (action has "")
};
