permit(
  principal,
  action,
  resource
) when {
  ((true && ({"": !true, "33\u{1}\0": ip("+")}[""])) && (resource in resource)) && true
};
