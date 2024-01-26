permit(
  principal,
  action,
  resource == a::"6\0"
) when {
  (true && (resource in resource)) && ((if (action in resource) then (if false then "" else "") else (if false then "" else "")) == (if (action in principal) then "\0\u{1f}\03" else ""))
};
