permit(
  principal == D::r3x3::a::"3333",
  action in [D::r3x3::Action::"action"],
  resource
) when {
  true && (principal in principal)
};
