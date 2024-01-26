permit(
  principal == a::"jj",
  action in [Action::"nks-`"],
  resource is a in a::"jj"
) when {
  (true && [context.greaterThan(2954362912118565482), resource, B0000::Eiq::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0:\0\0\0\0\u{1}", resource, "", !(!principal)]) && false
};
