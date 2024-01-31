% use tail -n -1 results/100_samples/single/test_synth_6_10_dc_lib20_3_* | grep -Eo '[+-]?[0-9]+([.][0-9]+)+'
% also grep "1 passed in" scp_test_adc_sd_int_2_* | grep -Eo '[+-]?[0-9]+([.][0-9]+)+'
% to get data from raw files

iter = 10000;
load('ADC_INT_DECOMPOSED');

A = ADC_INT_DECOMPOSED(1:30,:);

stata = bootstrp(iter, @mean, A);

resa = mean(stata);

meanci_a = bootci(iter, @mean, A);

resa = [resa; meanci_a];

resa = resa'

 %figure;
 %hold;
 % stat = bootstrp(iter, @mean, A);
 % for i = 1:size(stat,2)
 %    figure;
 %    hist(stat(:,i));
 %    title(['Histogram - Iteration ' num2str(i)]);
 %    legendInfo{i} = [num2str(i)];
 %    pause(1);
 %end

