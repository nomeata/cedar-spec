permit(
  principal is B::r,
  action in [B::Action::"action",B::Action::"action"],
  resource is B::r
) when {
  true && (B::Tbb::"4v6/" is B::r)
};
